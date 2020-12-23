%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow_0__t18_yellow_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:38 EDT 2019

% Result     : Theorem 3.09s
% Output     : Refutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :  441 (1049 expanded)
%              Number of leaves         :   61 ( 346 expanded)
%              Depth                    :   19
%              Number of atoms          : 2628 (6829 expanded)
%              Number of equality atoms :   65 ( 297 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17184,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f115,f143,f150,f157,f170,f178,f832,f2568,f2571,f2670,f2683,f2704,f2725,f2887,f2929,f3145,f8014,f8024,f10414,f10446,f10520,f10596,f10678,f11052,f11151,f11159,f11167,f11261,f11275,f11983,f12016,f12163,f14281,f14308,f14698,f15759,f15888,f16051,f16094,f16126,f16187,f16900,f17182])).

fof(f17182,plain,
    ( spl14_41
    | ~ spl14_120 ),
    inference(avatar_contradiction_clause,[],[f17179])).

fof(f17179,plain,
    ( $false
    | ~ spl14_41
    | ~ spl14_120 ),
    inference(resolution,[],[f17020,f2669])).

fof(f2669,plain,
    ( sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_120 ),
    inference(avatar_component_clause,[],[f2668])).

fof(f2668,plain,
    ( spl14_120
  <=> sP7(sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_120])])).

fof(f17020,plain,
    ( ! [X11] : ~ sP7(sK3,sK2,X11,sK0)
    | ~ spl14_41 ),
    inference(resolution,[],[f510,f66])).

fof(f66,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X2,X5)
      | ~ sP7(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k10_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X5,X6)
                          | ~ r1_orders_2(X0,X2,X6)
                          | ~ r1_orders_2(X0,X1,X6)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X5)
                      & r1_orders_2(X0,X1,X5) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X5] :
                  ( ( k10_lattice3(X0,X1,X2) = X5
                  <=> ( ! [X6] :
                          ( r1_orders_2(X0,X5,X6)
                          | ~ r1_orders_2(X0,X2,X6)
                          | ~ r1_orders_2(X0,X1,X6)
                          | ~ m1_subset_1(X6,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X5)
                      & r1_orders_2(X0,X1,X5) ) )
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              | ! [X3] :
                  ( ? [X4] :
                      ( ~ r1_orders_2(X0,X3,X4)
                      & r1_orders_2(X0,X2,X4)
                      & r1_orders_2(X0,X1,X4)
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X5] :
                      ( m1_subset_1(X5,u1_struct_0(X0))
                     => ( k10_lattice3(X0,X1,X2) = X5
                      <=> ( ! [X6] :
                              ( m1_subset_1(X6,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X6)
                                  & r1_orders_2(X0,X1,X6) )
                               => r1_orders_2(X0,X5,X6) ) )
                          & r1_orders_2(X0,X2,X5)
                          & r1_orders_2(X0,X1,X5) ) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v5_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ? [X3] :
                      ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( k10_lattice3(X0,X1,X2) = X3
                      <=> ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t18_yellow_0.p',d13_lattice3)).

fof(f510,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ spl14_41 ),
    inference(avatar_component_clause,[],[f509])).

fof(f509,plain,
    ( spl14_41
  <=> ~ r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_41])])).

fof(f16900,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_80
    | ~ spl14_82
    | ~ spl14_84
    | ~ spl14_118 ),
    inference(avatar_contradiction_clause,[],[f16899])).

fof(f16899,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_80
    | ~ spl14_82
    | ~ spl14_84
    | ~ spl14_118 ),
    inference(subsumption_resolution,[],[f16898,f1717])).

fof(f1717,plain,
    ( r1_orders_2(sK0,sK9(sK0,k2_tarski(sK1,sK2)),sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ spl14_82 ),
    inference(avatar_component_clause,[],[f1716])).

fof(f1716,plain,
    ( spl14_82
  <=> r1_orders_2(sK0,sK9(sK0,k2_tarski(sK1,sK2)),sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_82])])).

fof(f16898,plain,
    ( ~ r1_orders_2(sK0,sK9(sK0,k2_tarski(sK1,sK2)),sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_118 ),
    inference(subsumption_resolution,[],[f16897,f1711])).

fof(f1711,plain,
    ( r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ spl14_80 ),
    inference(avatar_component_clause,[],[f1710])).

fof(f1710,plain,
    ( spl14_80
  <=> r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_80])])).

fof(f16897,plain,
    ( ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK9(sK0,k2_tarski(sK1,sK2)),sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_84
    | ~ spl14_118 ),
    inference(subsumption_resolution,[],[f16896,f1723])).

fof(f1723,plain,
    ( r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ spl14_84 ),
    inference(avatar_component_clause,[],[f1722])).

fof(f1722,plain,
    ( spl14_84
  <=> r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_84])])).

fof(f16896,plain,
    ( ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK9(sK0,k2_tarski(sK1,sK2)),sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_118 ),
    inference(resolution,[],[f16750,f169])).

fof(f169,plain,
    ( r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl14_12
  <=> r1_yellow_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f16750,plain,
    ( ! [X12] :
        ( ~ r1_yellow_0(sK0,X12)
        | ~ r1_orders_2(sK0,sK2,sK9(sK0,X12))
        | ~ r1_orders_2(sK0,sK1,sK9(sK0,X12))
        | ~ r1_orders_2(sK0,sK9(sK0,X12),sK6(sK0,sK1,sK2,sK9(sK0,X12))) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_118 ),
    inference(subsumption_resolution,[],[f16749,f107])).

fof(f107,plain,
    ( v5_orders_2(sK0)
    | ~ spl14_0 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl14_0
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_0])])).

fof(f16749,plain,
    ( ! [X12] :
        ( ~ r1_orders_2(sK0,sK9(sK0,X12),sK6(sK0,sK1,sK2,sK9(sK0,X12)))
        | ~ r1_orders_2(sK0,sK2,sK9(sK0,X12))
        | ~ r1_orders_2(sK0,sK1,sK9(sK0,X12))
        | ~ v5_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X12) )
    | ~ spl14_2
    | ~ spl14_118 ),
    inference(subsumption_resolution,[],[f16732,f114])).

fof(f114,plain,
    ( l1_orders_2(sK0)
    | ~ spl14_2 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl14_2
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f16732,plain,
    ( ! [X12] :
        ( ~ r1_orders_2(sK0,sK9(sK0,X12),sK6(sK0,sK1,sK2,sK9(sK0,X12)))
        | ~ r1_orders_2(sK0,sK2,sK9(sK0,X12))
        | ~ r1_orders_2(sK0,sK1,sK9(sK0,X12))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X12) )
    | ~ spl14_118 ),
    inference(resolution,[],[f2663,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK9(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t18_yellow_0.p',t15_yellow_0)).

fof(f2663,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,sK6(sK0,sK1,sK2,X4))
        | ~ r1_orders_2(sK0,sK2,X4)
        | ~ r1_orders_2(sK0,sK1,X4) )
    | ~ spl14_118 ),
    inference(avatar_component_clause,[],[f2662])).

fof(f2662,plain,
    ( spl14_118
  <=> ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,sK6(sK0,sK1,sK2,X4))
        | ~ r1_orders_2(sK0,sK2,X4)
        | ~ r1_orders_2(sK0,sK1,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_118])])).

fof(f16187,plain,
    ( ~ spl14_32
    | ~ spl14_40
    | spl14_121
    | spl14_373 ),
    inference(avatar_contradiction_clause,[],[f16186])).

fof(f16186,plain,
    ( $false
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_121
    | ~ spl14_373 ),
    inference(subsumption_resolution,[],[f16185,f2666])).

fof(f2666,plain,
    ( ~ sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_121 ),
    inference(avatar_component_clause,[],[f2665])).

fof(f2665,plain,
    ( spl14_121
  <=> ~ sP7(sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_121])])).

fof(f16185,plain,
    ( sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_373 ),
    inference(subsumption_resolution,[],[f16184,f449])).

fof(f449,plain,
    ( r1_orders_2(sK0,sK1,sK3)
    | ~ spl14_32 ),
    inference(avatar_component_clause,[],[f448])).

fof(f448,plain,
    ( spl14_32
  <=> r1_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_32])])).

fof(f16184,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_40
    | ~ spl14_373 ),
    inference(subsumption_resolution,[],[f16169,f507])).

fof(f507,plain,
    ( r1_orders_2(sK0,sK2,sK3)
    | ~ spl14_40 ),
    inference(avatar_component_clause,[],[f506])).

fof(f506,plain,
    ( spl14_40
  <=> r1_orders_2(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_40])])).

fof(f16169,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_373 ),
    inference(resolution,[],[f16093,f63])).

fof(f63,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X2,sK8(X0,X1,X2,X5))
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | sP7(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16093,plain,
    ( ~ r1_orders_2(sK0,sK2,sK8(sK0,sK1,sK2,sK3))
    | ~ spl14_373 ),
    inference(avatar_component_clause,[],[f16092])).

fof(f16092,plain,
    ( spl14_373
  <=> ~ r1_orders_2(sK0,sK2,sK8(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_373])])).

fof(f16126,plain,
    ( ~ spl14_32
    | ~ spl14_40
    | spl14_121
    | spl14_371 ),
    inference(avatar_contradiction_clause,[],[f16125])).

fof(f16125,plain,
    ( $false
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_121
    | ~ spl14_371 ),
    inference(subsumption_resolution,[],[f16124,f2666])).

fof(f16124,plain,
    ( sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_371 ),
    inference(subsumption_resolution,[],[f16123,f449])).

fof(f16123,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_40
    | ~ spl14_371 ),
    inference(subsumption_resolution,[],[f16108,f507])).

fof(f16108,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_371 ),
    inference(resolution,[],[f16087,f62])).

fof(f62,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X1,sK8(X0,X1,X2,X5))
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | sP7(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f16087,plain,
    ( ~ r1_orders_2(sK0,sK1,sK8(sK0,sK1,sK2,sK3))
    | ~ spl14_371 ),
    inference(avatar_component_clause,[],[f16086])).

fof(f16086,plain,
    ( spl14_371
  <=> ~ r1_orders_2(sK0,sK1,sK8(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_371])])).

fof(f16094,plain,
    ( ~ spl14_371
    | ~ spl14_373
    | ~ spl14_10
    | spl14_123
    | ~ spl14_128 ),
    inference(avatar_split_clause,[],[f16080,f2916,f2681,f162,f16092,f16086])).

fof(f162,plain,
    ( spl14_10
  <=> sP4(sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f2681,plain,
    ( spl14_123
  <=> ~ r1_orders_2(sK0,sK3,sK8(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_123])])).

fof(f2916,plain,
    ( spl14_128
  <=> m1_subset_1(sK8(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_128])])).

fof(f16080,plain,
    ( ~ r1_orders_2(sK0,sK2,sK8(sK0,sK1,sK2,sK3))
    | ~ r1_orders_2(sK0,sK1,sK8(sK0,sK1,sK2,sK3))
    | ~ spl14_10
    | ~ spl14_123
    | ~ spl14_128 ),
    inference(resolution,[],[f16079,f163])).

fof(f163,plain,
    ( sP4(sK3,sK2,sK1,sK0)
    | ~ spl14_10 ),
    inference(avatar_component_clause,[],[f162])).

fof(f16079,plain,
    ( ! [X4,X5] :
        ( ~ sP4(sK3,X5,X4,sK0)
        | ~ r1_orders_2(sK0,X5,sK8(sK0,sK1,sK2,sK3))
        | ~ r1_orders_2(sK0,X4,sK8(sK0,sK1,sK2,sK3)) )
    | ~ spl14_123
    | ~ spl14_128 ),
    inference(subsumption_resolution,[],[f2688,f2917])).

fof(f2917,plain,
    ( m1_subset_1(sK8(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ spl14_128 ),
    inference(avatar_component_clause,[],[f2916])).

fof(f2688,plain,
    ( ! [X4,X5] :
        ( ~ r1_orders_2(sK0,X4,sK8(sK0,sK1,sK2,sK3))
        | ~ r1_orders_2(sK0,X5,sK8(sK0,sK1,sK2,sK3))
        | ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
        | ~ sP4(sK3,X5,X4,sK0) )
    | ~ spl14_123 ),
    inference(resolution,[],[f2682,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X4)
      | ~ r1_orders_2(X0,X1,X4)
      | ~ r1_orders_2(X0,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ sP4(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                        | k10_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(X0,X3,X5)
                            & r1_orders_2(X0,X2,X5)
                            & r1_orders_2(X0,X1,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ r1_orders_2(X0,X2,X3)
                        | ~ r1_orders_2(X0,X1,X3) )
                      & r1_yellow_0(X0,k2_tarski(X1,X2))
                      & k10_lattice3(X0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( ~ r1_yellow_0(X0,k2_tarski(X1,X2))
                        | k10_lattice3(X0,X1,X2) != X3 )
                      & ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) )
                    | ( ( ? [X5] :
                            ( ~ r1_orders_2(X0,X3,X5)
                            & r1_orders_2(X0,X2,X5)
                            & r1_orders_2(X0,X1,X5)
                            & m1_subset_1(X5,u1_struct_0(X0)) )
                        | ~ r1_orders_2(X0,X2,X3)
                        | ~ r1_orders_2(X0,X1,X3) )
                      & r1_yellow_0(X0,k2_tarski(X1,X2))
                      & k10_lattice3(X0,X1,X2) = X3 ) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) )
                       => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                          & k10_lattice3(X0,X1,X2) = X3 ) )
                      & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                          & k10_lattice3(X0,X1,X2) = X3 )
                       => ( ! [X5] :
                              ( m1_subset_1(X5,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X5)
                                  & r1_orders_2(X0,X1,X5) )
                               => r1_orders_2(X0,X3,X5) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) )
                       => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                          & k10_lattice3(X0,X1,X2) = X3 ) )
                      & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                          & k10_lattice3(X0,X1,X2) = X3 )
                       => ( ! [X4] :
                              ( m1_subset_1(X4,u1_struct_0(X0))
                             => ( ( r1_orders_2(X0,X2,X4)
                                  & r1_orders_2(X0,X1,X4) )
                               => r1_orders_2(X0,X3,X4) ) )
                          & r1_orders_2(X0,X2,X3)
                          & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                     => ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 ) )
                    & ( ( r1_yellow_0(X0,k2_tarski(X1,X2))
                        & k10_lattice3(X0,X1,X2) = X3 )
                     => ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( ( r1_orders_2(X0,X2,X4)
                                & r1_orders_2(X0,X1,X4) )
                             => r1_orders_2(X0,X3,X4) ) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t18_yellow_0.p',t18_yellow_0)).

fof(f2682,plain,
    ( ~ r1_orders_2(sK0,sK3,sK8(sK0,sK1,sK2,sK3))
    | ~ spl14_123 ),
    inference(avatar_component_clause,[],[f2681])).

fof(f16051,plain,
    ( ~ spl14_10
    | spl14_125
    | ~ spl14_132
    | ~ spl14_366
    | ~ spl14_368 ),
    inference(avatar_contradiction_clause,[],[f16050])).

fof(f16050,plain,
    ( $false
    | ~ spl14_10
    | ~ spl14_125
    | ~ spl14_132
    | ~ spl14_366
    | ~ spl14_368 ),
    inference(subsumption_resolution,[],[f15889,f15586])).

fof(f15586,plain,
    ( r1_orders_2(sK0,sK1,sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ spl14_368 ),
    inference(avatar_component_clause,[],[f15585])).

fof(f15585,plain,
    ( spl14_368
  <=> r1_orders_2(sK0,sK1,sK10(sK0,k2_tarski(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_368])])).

fof(f15889,plain,
    ( ~ r1_orders_2(sK0,sK1,sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ spl14_10
    | ~ spl14_125
    | ~ spl14_132
    | ~ spl14_366 ),
    inference(subsumption_resolution,[],[f15628,f15580])).

fof(f15580,plain,
    ( r1_orders_2(sK0,sK2,sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ spl14_366 ),
    inference(avatar_component_clause,[],[f15579])).

fof(f15579,plain,
    ( spl14_366
  <=> r1_orders_2(sK0,sK2,sK10(sK0,k2_tarski(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_366])])).

fof(f15628,plain,
    ( ~ r1_orders_2(sK0,sK2,sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ r1_orders_2(sK0,sK1,sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ spl14_10
    | ~ spl14_125
    | ~ spl14_132 ),
    inference(resolution,[],[f15627,f163])).

fof(f15627,plain,
    ( ! [X4,X5] :
        ( ~ sP4(sK3,X5,X4,sK0)
        | ~ r1_orders_2(sK0,X5,sK10(sK0,k2_tarski(sK1,sK2),sK3))
        | ~ r1_orders_2(sK0,X4,sK10(sK0,k2_tarski(sK1,sK2),sK3)) )
    | ~ spl14_125
    | ~ spl14_132 ),
    inference(subsumption_resolution,[],[f2709,f3120])).

fof(f3120,plain,
    ( m1_subset_1(sK10(sK0,k2_tarski(sK1,sK2),sK3),u1_struct_0(sK0))
    | ~ spl14_132 ),
    inference(avatar_component_clause,[],[f3119])).

fof(f3119,plain,
    ( spl14_132
  <=> m1_subset_1(sK10(sK0,k2_tarski(sK1,sK2),sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_132])])).

fof(f2709,plain,
    ( ! [X4,X5] :
        ( ~ r1_orders_2(sK0,X4,sK10(sK0,k2_tarski(sK1,sK2),sK3))
        | ~ r1_orders_2(sK0,X5,sK10(sK0,k2_tarski(sK1,sK2),sK3))
        | ~ m1_subset_1(sK10(sK0,k2_tarski(sK1,sK2),sK3),u1_struct_0(sK0))
        | ~ sP4(sK3,X5,X4,sK0) )
    | ~ spl14_125 ),
    inference(resolution,[],[f2703,f43])).

fof(f2703,plain,
    ( ~ r1_orders_2(sK0,sK3,sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ spl14_125 ),
    inference(avatar_component_clause,[],[f2702])).

fof(f2702,plain,
    ( spl14_125
  <=> ~ r1_orders_2(sK0,sK3,sK10(sK0,k2_tarski(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_125])])).

fof(f15888,plain,
    ( ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_126
    | ~ spl14_132
    | spl14_369 ),
    inference(avatar_contradiction_clause,[],[f15887])).

fof(f15887,plain,
    ( $false
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_126
    | ~ spl14_132
    | ~ spl14_369 ),
    inference(subsumption_resolution,[],[f15882,f149])).

fof(f149,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl14_6
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f15882,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_126
    | ~ spl14_132
    | ~ spl14_369 ),
    inference(resolution,[],[f15626,f2724])).

fof(f2724,plain,
    ( r2_lattice3(sK0,k2_tarski(sK1,sK2),sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ spl14_126 ),
    inference(avatar_component_clause,[],[f2723])).

fof(f2723,plain,
    ( spl14_126
  <=> r2_lattice3(sK0,k2_tarski(sK1,sK2),sK10(sK0,k2_tarski(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_126])])).

fof(f15626,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,k2_tarski(sK1,X3),sK10(sK0,k2_tarski(sK1,sK2),sK3))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_132
    | ~ spl14_369 ),
    inference(subsumption_resolution,[],[f15625,f3120])).

fof(f15625,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,X3),sK10(sK0,k2_tarski(sK1,sK2),sK3))
        | ~ m1_subset_1(sK10(sK0,k2_tarski(sK1,sK2),sK3),u1_struct_0(sK0)) )
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_369 ),
    inference(subsumption_resolution,[],[f15612,f156])).

fof(f156,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl14_8 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl14_8
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f15612,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,X3),sK10(sK0,k2_tarski(sK1,sK2),sK3))
        | ~ m1_subset_1(sK10(sK0,k2_tarski(sK1,sK2),sK3),u1_struct_0(sK0)) )
    | ~ spl14_2
    | ~ spl14_369 ),
    inference(resolution,[],[f15589,f119])).

fof(f119,plain,
    ( ! [X14,X12,X13] :
        ( r1_orders_2(sK0,X13,X12)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ m1_subset_1(X14,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_tarski(X13,X14),X12)
        | ~ m1_subset_1(X12,u1_struct_0(sK0)) )
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                     => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) ) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t18_yellow_0.p',t8_yellow_0)).

fof(f15589,plain,
    ( ~ r1_orders_2(sK0,sK1,sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ spl14_369 ),
    inference(avatar_component_clause,[],[f15588])).

fof(f15588,plain,
    ( spl14_369
  <=> ~ r1_orders_2(sK0,sK1,sK10(sK0,k2_tarski(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_369])])).

fof(f15759,plain,
    ( ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_126
    | ~ spl14_132
    | spl14_367 ),
    inference(avatar_contradiction_clause,[],[f15758])).

fof(f15758,plain,
    ( $false
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_126
    | ~ spl14_132
    | ~ spl14_367 ),
    inference(subsumption_resolution,[],[f15753,f156])).

fof(f15753,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_126
    | ~ spl14_132
    | ~ spl14_367 ),
    inference(resolution,[],[f15606,f2724])).

fof(f15606,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,k2_tarski(X2,sK2),sK10(sK0,k2_tarski(sK1,sK2),sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_132
    | ~ spl14_367 ),
    inference(subsumption_resolution,[],[f15605,f3120])).

fof(f15605,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_tarski(X2,sK2),sK10(sK0,k2_tarski(sK1,sK2),sK3))
        | ~ m1_subset_1(sK10(sK0,k2_tarski(sK1,sK2),sK3),u1_struct_0(sK0)) )
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_367 ),
    inference(subsumption_resolution,[],[f15593,f149])).

fof(f15593,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_tarski(X2,sK2),sK10(sK0,k2_tarski(sK1,sK2),sK3))
        | ~ m1_subset_1(sK10(sK0,k2_tarski(sK1,sK2),sK3),u1_struct_0(sK0)) )
    | ~ spl14_2
    | ~ spl14_367 ),
    inference(resolution,[],[f15583,f120])).

fof(f120,plain,
    ( ! [X17,X15,X16] :
        ( r1_orders_2(sK0,X17,X15)
        | ~ m1_subset_1(X16,u1_struct_0(sK0))
        | ~ m1_subset_1(X17,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_tarski(X16,X17),X15)
        | ~ m1_subset_1(X15,u1_struct_0(sK0)) )
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X3,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15583,plain,
    ( ~ r1_orders_2(sK0,sK2,sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ spl14_367 ),
    inference(avatar_component_clause,[],[f15582])).

fof(f15582,plain,
    ( spl14_367
  <=> ~ r1_orders_2(sK0,sK2,sK10(sK0,k2_tarski(sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_367])])).

fof(f14698,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | spl14_13
    | ~ spl14_102
    | spl14_133 ),
    inference(avatar_contradiction_clause,[],[f14697])).

fof(f14697,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_13
    | ~ spl14_102
    | ~ spl14_133 ),
    inference(subsumption_resolution,[],[f14349,f166])).

fof(f166,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl14_13
  <=> ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_13])])).

fof(f14349,plain,
    ( r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_102
    | ~ spl14_133 ),
    inference(subsumption_resolution,[],[f14348,f107])).

fof(f14348,plain,
    ( ~ v5_orders_2(sK0)
    | r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_102
    | ~ spl14_133 ),
    inference(subsumption_resolution,[],[f14347,f2191])).

fof(f2191,plain,
    ( r2_lattice3(sK0,k2_tarski(sK1,sK2),sK3)
    | ~ spl14_102 ),
    inference(avatar_component_clause,[],[f2190])).

fof(f2190,plain,
    ( spl14_102
  <=> r2_lattice3(sK0,k2_tarski(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_102])])).

fof(f14347,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK3)
    | ~ v5_orders_2(sK0)
    | r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_133 ),
    inference(subsumption_resolution,[],[f14346,f142])).

fof(f142,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl14_4 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl14_4
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f14346,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK3)
    | ~ v5_orders_2(sK0)
    | r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_2
    | ~ spl14_133 ),
    inference(subsumption_resolution,[],[f3128,f114])).

fof(f3128,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK3)
    | ~ v5_orders_2(sK0)
    | r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_133 ),
    inference(resolution,[],[f3123,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3123,plain,
    ( ~ m1_subset_1(sK10(sK0,k2_tarski(sK1,sK2),sK3),u1_struct_0(sK0))
    | ~ spl14_133 ),
    inference(avatar_component_clause,[],[f3122])).

fof(f3122,plain,
    ( spl14_133
  <=> ~ m1_subset_1(sK10(sK0,k2_tarski(sK1,sK2),sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_133])])).

fof(f14308,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | spl14_15
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_120
    | spl14_323 ),
    inference(avatar_contradiction_clause,[],[f14307])).

fof(f14307,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_15
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_120
    | ~ spl14_323 ),
    inference(subsumption_resolution,[],[f14306,f174])).

fof(f174,plain,
    ( k10_lattice3(sK0,sK1,sK2) != sK3
    | ~ spl14_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl14_15
  <=> k10_lattice3(sK0,sK1,sK2) != sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_15])])).

fof(f14306,plain,
    ( k10_lattice3(sK0,sK1,sK2) = sK3
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_120
    | ~ spl14_323 ),
    inference(subsumption_resolution,[],[f14291,f2669])).

fof(f14291,plain,
    ( ~ sP7(sK3,sK2,sK1,sK0)
    | k10_lattice3(sK0,sK1,sK2) = sK3
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_323 ),
    inference(resolution,[],[f12211,f142])).

fof(f12211,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_323 ),
    inference(subsumption_resolution,[],[f12210,f156])).

fof(f12210,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_323 ),
    inference(subsumption_resolution,[],[f12209,f507])).

fof(f12209,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,sK3)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_32
    | ~ spl14_323 ),
    inference(subsumption_resolution,[],[f12208,f449])).

fof(f12208,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_323 ),
    inference(subsumption_resolution,[],[f12207,f142])).

fof(f12207,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_323 ),
    inference(subsumption_resolution,[],[f12196,f149])).

fof(f12196,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_323 ),
    inference(resolution,[],[f12162,f131])).

fof(f131,plain,
    ( ! [X6,X4,X7,X5] :
        ( r1_orders_2(sK0,X5,sK6(sK0,X4,X5,X6))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X6)
        | ~ r1_orders_2(sK0,X5,X6)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ sP7(X7,X5,X4,sK0)
        | k10_lattice3(sK0,X4,X5) = X7 )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f117,f107])).

fof(f117,plain,
    ( ! [X6,X4,X7,X5] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X6)
        | ~ r1_orders_2(sK0,X5,X6)
        | r1_orders_2(sK0,X5,sK6(sK0,X4,X5,X6))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ sP7(X7,X5,X4,sK0)
        | k10_lattice3(sK0,X4,X5) = X7 )
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f73])).

fof(f73,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP7(X5,X2,X1,X0)
      | k10_lattice3(X0,X1,X2) = X5 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12162,plain,
    ( ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK3))
    | ~ spl14_323 ),
    inference(avatar_component_clause,[],[f12161])).

fof(f12161,plain,
    ( spl14_323
  <=> ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_323])])).

fof(f14281,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | spl14_15
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_120
    | spl14_321 ),
    inference(avatar_contradiction_clause,[],[f14280])).

fof(f14280,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_15
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_120
    | ~ spl14_321 ),
    inference(subsumption_resolution,[],[f14279,f174])).

fof(f14279,plain,
    ( k10_lattice3(sK0,sK1,sK2) = sK3
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_120
    | ~ spl14_321 ),
    inference(subsumption_resolution,[],[f14264,f2669])).

fof(f14264,plain,
    ( ~ sP7(sK3,sK2,sK1,sK0)
    | k10_lattice3(sK0,sK1,sK2) = sK3
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_321 ),
    inference(resolution,[],[f12186,f142])).

fof(f12186,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_321 ),
    inference(subsumption_resolution,[],[f12185,f156])).

fof(f12185,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_321 ),
    inference(subsumption_resolution,[],[f12184,f507])).

fof(f12184,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,sK3)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_32
    | ~ spl14_321 ),
    inference(subsumption_resolution,[],[f12183,f449])).

fof(f12183,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_321 ),
    inference(subsumption_resolution,[],[f12182,f142])).

fof(f12182,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_321 ),
    inference(subsumption_resolution,[],[f12171,f149])).

fof(f12171,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_321 ),
    inference(resolution,[],[f12156,f130])).

fof(f130,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_orders_2(sK0,X0,sK6(sK0,X0,X1,X2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ sP7(X3,X1,X0,sK0)
        | k10_lattice3(sK0,X0,X1) = X3 )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f116,f107])).

fof(f116,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,sK6(sK0,X0,X1,X2))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ sP7(X3,X1,X0,sK0)
        | k10_lattice3(sK0,X0,X1) = X3 )
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f72])).

fof(f72,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP7(X5,X2,X1,X0)
      | k10_lattice3(X0,X1,X2) = X5 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12156,plain,
    ( ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK3))
    | ~ spl14_321 ),
    inference(avatar_component_clause,[],[f12155])).

fof(f12155,plain,
    ( spl14_321
  <=> ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_321])])).

fof(f12163,plain,
    ( ~ spl14_321
    | ~ spl14_323
    | ~ spl14_10
    | spl14_295
    | ~ spl14_296 ),
    inference(avatar_split_clause,[],[f12141,f11354,f11311,f162,f12161,f12155])).

fof(f11311,plain,
    ( spl14_295
  <=> ~ r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_295])])).

fof(f11354,plain,
    ( spl14_296
  <=> m1_subset_1(sK6(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_296])])).

fof(f12141,plain,
    ( ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK3))
    | ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK3))
    | ~ spl14_10
    | ~ spl14_295
    | ~ spl14_296 ),
    inference(resolution,[],[f12140,f163])).

fof(f12140,plain,
    ( ! [X4,X5] :
        ( ~ sP4(sK3,X5,X4,sK0)
        | ~ r1_orders_2(sK0,X5,sK6(sK0,sK1,sK2,sK3))
        | ~ r1_orders_2(sK0,X4,sK6(sK0,sK1,sK2,sK3)) )
    | ~ spl14_295
    | ~ spl14_296 ),
    inference(subsumption_resolution,[],[f12027,f11355])).

fof(f11355,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ spl14_296 ),
    inference(avatar_component_clause,[],[f11354])).

fof(f12027,plain,
    ( ! [X4,X5] :
        ( ~ r1_orders_2(sK0,X4,sK6(sK0,sK1,sK2,sK3))
        | ~ r1_orders_2(sK0,X5,sK6(sK0,sK1,sK2,sK3))
        | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
        | ~ sP4(sK3,X5,X4,sK0) )
    | ~ spl14_295 ),
    inference(resolution,[],[f11312,f43])).

fof(f11312,plain,
    ( ~ r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK2,sK3))
    | ~ spl14_295 ),
    inference(avatar_component_clause,[],[f11311])).

fof(f12016,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | spl14_15
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_120
    | ~ spl14_294 ),
    inference(avatar_contradiction_clause,[],[f12015])).

fof(f12015,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_15
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_120
    | ~ spl14_294 ),
    inference(subsumption_resolution,[],[f12014,f11309])).

fof(f11309,plain,
    ( r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK2,sK3))
    | ~ spl14_294 ),
    inference(avatar_component_clause,[],[f11308])).

fof(f11308,plain,
    ( spl14_294
  <=> r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_294])])).

fof(f12014,plain,
    ( ~ r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK2,sK3))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_15
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_120 ),
    inference(subsumption_resolution,[],[f12013,f507])).

fof(f12013,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK2,sK3))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_15
    | ~ spl14_32
    | ~ spl14_120 ),
    inference(subsumption_resolution,[],[f12001,f449])).

fof(f12001,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK3,sK6(sK0,sK1,sK2,sK3))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_15
    | ~ spl14_120 ),
    inference(resolution,[],[f11993,f142])).

fof(f11993,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2,X0)) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_15
    | ~ spl14_120 ),
    inference(subsumption_resolution,[],[f11992,f174])).

fof(f11992,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2,X0))
        | k10_lattice3(sK0,sK1,sK2) = sK3 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_120 ),
    inference(subsumption_resolution,[],[f11991,f156])).

fof(f11991,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2,X0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | k10_lattice3(sK0,sK1,sK2) = sK3 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_120 ),
    inference(subsumption_resolution,[],[f11990,f142])).

fof(f11990,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2,X0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | k10_lattice3(sK0,sK1,sK2) = sK3 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_120 ),
    inference(subsumption_resolution,[],[f11138,f149])).

fof(f11138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,sK1,sK2,X0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | k10_lattice3(sK0,sK1,sK2) = sK3 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_120 ),
    inference(resolution,[],[f2669,f132])).

fof(f132,plain,
    ( ! [X10,X8,X11,X9] :
        ( ~ sP7(X11,X9,X8,sK0)
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X10)
        | ~ r1_orders_2(sK0,X9,X10)
        | ~ r1_orders_2(sK0,X10,sK6(sK0,X8,X9,X10))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | k10_lattice3(sK0,X8,X9) = X11 )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f118,f107])).

fof(f118,plain,
    ( ! [X10,X8,X11,X9] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X8,X10)
        | ~ r1_orders_2(sK0,X9,X10)
        | ~ r1_orders_2(sK0,X10,sK6(sK0,X8,X9,X10))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ sP7(X11,X9,X8,sK0)
        | k10_lattice3(sK0,X8,X9) = X11 )
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f74])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP7(X5,X2,X1,X0)
      | k10_lattice3(X0,X1,X2) = X5 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11983,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | spl14_15
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_120
    | spl14_297 ),
    inference(avatar_contradiction_clause,[],[f11982])).

fof(f11982,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_15
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_120
    | ~ spl14_297 ),
    inference(subsumption_resolution,[],[f11981,f174])).

fof(f11981,plain,
    ( k10_lattice3(sK0,sK1,sK2) = sK3
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_120
    | ~ spl14_297 ),
    inference(subsumption_resolution,[],[f11969,f2669])).

fof(f11969,plain,
    ( ~ sP7(sK3,sK2,sK1,sK0)
    | k10_lattice3(sK0,sK1,sK2) = sK3
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_297 ),
    inference(resolution,[],[f11376,f142])).

fof(f11376,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_297 ),
    inference(subsumption_resolution,[],[f11375,f114])).

fof(f11375,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_297 ),
    inference(subsumption_resolution,[],[f11374,f507])).

fof(f11374,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK2,sK3)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_297 ),
    inference(subsumption_resolution,[],[f11373,f449])).

fof(f11373,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_297 ),
    inference(subsumption_resolution,[],[f11372,f142])).

fof(f11372,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_297 ),
    inference(subsumption_resolution,[],[f11371,f149])).

fof(f11371,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_8
    | ~ spl14_297 ),
    inference(subsumption_resolution,[],[f11370,f156])).

fof(f11370,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_0
    | ~ spl14_297 ),
    inference(subsumption_resolution,[],[f11364,f107])).

fof(f11364,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,sK3)
        | ~ r1_orders_2(sK0,sK2,sK3)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ sP7(X0,sK2,sK1,sK0)
        | k10_lattice3(sK0,sK1,sK2) = X0 )
    | ~ spl14_297 ),
    inference(resolution,[],[f11358,f71])).

fof(f71,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ sP7(X5,X2,X1,X0)
      | k10_lattice3(X0,X1,X2) = X5 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11358,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ spl14_297 ),
    inference(avatar_component_clause,[],[f11357])).

fof(f11357,plain,
    ( spl14_297
  <=> ~ m1_subset_1(sK6(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_297])])).

fof(f11275,plain,
    ( ~ spl14_10
    | ~ spl14_12
    | ~ spl14_14 ),
    inference(avatar_contradiction_clause,[],[f11274])).

fof(f11274,plain,
    ( $false
    | ~ spl14_10
    | ~ spl14_12
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f11263,f163])).

fof(f11263,plain,
    ( ~ sP4(sK3,sK2,sK1,sK0)
    | ~ spl14_12
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f2961,f169])).

fof(f2961,plain,
    ( ~ sP4(sK3,sK2,sK1,sK0)
    | ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_14 ),
    inference(superposition,[],[f97,f177])).

fof(f177,plain,
    ( k10_lattice3(sK0,sK1,sK2) = sK3
    | ~ spl14_14 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl14_14
  <=> k10_lattice3(sK0,sK1,sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_14])])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(k10_lattice3(X0,X1,X2),X2,X1,X0)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_lattice3(X0,X1,X2) != X3
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ sP4(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f11261,plain,
    ( ~ spl14_120
    | ~ spl14_286
    | ~ spl14_288
    | ~ spl14_290
    | spl14_293 ),
    inference(avatar_contradiction_clause,[],[f11260])).

fof(f11260,plain,
    ( $false
    | ~ spl14_120
    | ~ spl14_286
    | ~ spl14_288
    | ~ spl14_290
    | ~ spl14_293 ),
    inference(subsumption_resolution,[],[f11259,f11150])).

fof(f11150,plain,
    ( r1_orders_2(sK0,sK1,sK5)
    | ~ spl14_288 ),
    inference(avatar_component_clause,[],[f11149])).

fof(f11149,plain,
    ( spl14_288
  <=> r1_orders_2(sK0,sK1,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_288])])).

fof(f11259,plain,
    ( ~ r1_orders_2(sK0,sK1,sK5)
    | ~ spl14_120
    | ~ spl14_286
    | ~ spl14_290
    | ~ spl14_293 ),
    inference(subsumption_resolution,[],[f11257,f11158])).

fof(f11158,plain,
    ( r1_orders_2(sK0,sK2,sK5)
    | ~ spl14_290 ),
    inference(avatar_component_clause,[],[f11157])).

fof(f11157,plain,
    ( spl14_290
  <=> r1_orders_2(sK0,sK2,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_290])])).

fof(f11257,plain,
    ( ~ r1_orders_2(sK0,sK2,sK5)
    | ~ r1_orders_2(sK0,sK1,sK5)
    | ~ spl14_120
    | ~ spl14_286
    | ~ spl14_293 ),
    inference(resolution,[],[f11187,f2669])).

fof(f11187,plain,
    ( ! [X8,X9] :
        ( ~ sP7(sK3,X9,X8,sK0)
        | ~ r1_orders_2(sK0,X9,sK5)
        | ~ r1_orders_2(sK0,X8,sK5) )
    | ~ spl14_286
    | ~ spl14_293 ),
    inference(subsumption_resolution,[],[f11175,f11051])).

fof(f11051,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ spl14_286 ),
    inference(avatar_component_clause,[],[f11050])).

fof(f11050,plain,
    ( spl14_286
  <=> m1_subset_1(sK5,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_286])])).

fof(f11175,plain,
    ( ! [X8,X9] :
        ( ~ r1_orders_2(sK0,X8,sK5)
        | ~ r1_orders_2(sK0,X9,sK5)
        | ~ m1_subset_1(sK5,u1_struct_0(sK0))
        | ~ sP7(sK3,X9,X8,sK0) )
    | ~ spl14_293 ),
    inference(resolution,[],[f11166,f60])).

fof(f60,plain,(
    ! [X6,X2,X0,X5,X1] :
      ( r1_orders_2(X0,X5,X6)
      | ~ r1_orders_2(X0,X1,X6)
      | ~ r1_orders_2(X0,X2,X6)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ sP7(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11166,plain,
    ( ~ r1_orders_2(sK0,sK3,sK5)
    | ~ spl14_293 ),
    inference(avatar_component_clause,[],[f11165])).

fof(f11165,plain,
    ( spl14_293
  <=> ~ r1_orders_2(sK0,sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_293])])).

fof(f11167,plain,
    ( ~ spl14_293
    | spl14_11
    | ~ spl14_32
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f11160,f506,f448,f159,f11165])).

fof(f159,plain,
    ( spl14_11
  <=> ~ sP4(sK3,sK2,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f11160,plain,
    ( ~ r1_orders_2(sK0,sK3,sK5)
    | ~ spl14_11
    | ~ spl14_32
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f11044,f449])).

fof(f11044,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK3,sK5)
    | ~ spl14_11
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f2930,f160])).

fof(f160,plain,
    ( ~ sP4(sK3,sK2,sK1,sK0)
    | ~ spl14_11 ),
    inference(avatar_component_clause,[],[f159])).

fof(f2930,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK3,sK5)
    | sP4(sK3,sK2,sK1,sK0)
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f47,f507])).

fof(f47,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK3,sK5)
    | sP4(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f11159,plain,
    ( spl14_290
    | spl14_11
    | ~ spl14_32
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f11152,f506,f448,f159,f11157])).

fof(f11152,plain,
    ( r1_orders_2(sK0,sK2,sK5)
    | ~ spl14_11
    | ~ spl14_32
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f11043,f449])).

fof(f11043,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | r1_orders_2(sK0,sK2,sK5)
    | ~ spl14_11
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f2931,f160])).

fof(f2931,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | r1_orders_2(sK0,sK2,sK5)
    | sP4(sK3,sK2,sK1,sK0)
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f46,f507])).

fof(f46,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK2,sK5)
    | sP4(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f11151,plain,
    ( spl14_288
    | spl14_11
    | ~ spl14_32
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f11133,f506,f448,f159,f11149])).

fof(f11133,plain,
    ( r1_orders_2(sK0,sK1,sK5)
    | ~ spl14_11
    | ~ spl14_32
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f11042,f449])).

fof(f11042,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | r1_orders_2(sK0,sK1,sK5)
    | ~ spl14_11
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f2932,f160])).

fof(f2932,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | r1_orders_2(sK0,sK1,sK5)
    | sP4(sK3,sK2,sK1,sK0)
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f45,f507])).

fof(f45,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | r1_orders_2(sK0,sK1,sK5)
    | sP4(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f11052,plain,
    ( spl14_286
    | spl14_11
    | ~ spl14_32
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f11045,f506,f448,f159,f11050])).

fof(f11045,plain,
    ( m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ spl14_11
    | ~ spl14_32
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f11041,f449])).

fof(f11041,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | m1_subset_1(sK5,u1_struct_0(sK0))
    | ~ spl14_11
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f2933,f160])).

fof(f2933,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | m1_subset_1(sK5,u1_struct_0(sK0))
    | sP4(sK3,sK2,sK1,sK0)
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f44,f507])).

fof(f44,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | m1_subset_1(sK5,u1_struct_0(sK0))
    | sP4(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f10678,plain,
    ( spl14_33
    | ~ spl14_120 ),
    inference(avatar_contradiction_clause,[],[f10677])).

fof(f10677,plain,
    ( $false
    | ~ spl14_33
    | ~ spl14_120 ),
    inference(subsumption_resolution,[],[f2669,f2943])).

fof(f2943,plain,
    ( ! [X10] : ~ sP7(sK3,X10,sK1,sK0)
    | ~ spl14_33 ),
    inference(resolution,[],[f452,f65])).

fof(f65,plain,(
    ! [X2,X0,X5,X1] :
      ( r1_orders_2(X0,X1,X5)
      | ~ sP7(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f452,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ spl14_33 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl14_33
  <=> ~ r1_orders_2(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_33])])).

fof(f10596,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_12
    | spl14_81
    | ~ spl14_114 ),
    inference(avatar_contradiction_clause,[],[f10595])).

fof(f10595,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_12
    | ~ spl14_81
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f10594,f169])).

fof(f10594,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_81
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f10590,f149])).

fof(f10590,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_81
    | ~ spl14_114 ),
    inference(resolution,[],[f10552,f136])).

fof(f136,plain,
    ( ! [X36] :
        ( r2_lattice3(sK0,X36,sK9(sK0,X36))
        | ~ r1_yellow_0(sK0,X36) )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f128,f107])).

fof(f128,plain,
    ( ! [X36] :
        ( ~ v5_orders_2(sK0)
        | r2_lattice3(sK0,X36,sK9(sK0,X36))
        | ~ r1_yellow_0(sK0,X36) )
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | r2_lattice3(X0,X1,sK9(X0,X1))
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10552,plain,
    ( ! [X3] :
        ( ~ r2_lattice3(sK0,k2_tarski(sK1,X3),sK9(sK0,k2_tarski(sK1,sK2)))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_81
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f10551,f2551])).

fof(f2551,plain,
    ( m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ spl14_114 ),
    inference(avatar_component_clause,[],[f2550])).

fof(f2550,plain,
    ( spl14_114
  <=> m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_114])])).

fof(f10551,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,X3),sK9(sK0,k2_tarski(sK1,sK2)))
        | ~ m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0)) )
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_81 ),
    inference(subsumption_resolution,[],[f10538,f156])).

fof(f10538,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_tarski(sK1,X3),sK9(sK0,k2_tarski(sK1,sK2)))
        | ~ m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0)) )
    | ~ spl14_2
    | ~ spl14_81 ),
    inference(resolution,[],[f1714,f119])).

fof(f1714,plain,
    ( ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ spl14_81 ),
    inference(avatar_component_clause,[],[f1713])).

fof(f1713,plain,
    ( spl14_81
  <=> ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_81])])).

fof(f10520,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_14
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | spl14_121
    | spl14_285 ),
    inference(avatar_contradiction_clause,[],[f10519])).

fof(f10519,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_14
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | ~ spl14_121
    | ~ spl14_285 ),
    inference(subsumption_resolution,[],[f10518,f2666])).

fof(f10518,plain,
    ( sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_14
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | ~ spl14_285 ),
    inference(forward_demodulation,[],[f10517,f177])).

fof(f10517,plain,
    ( sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | ~ spl14_285 ),
    inference(subsumption_resolution,[],[f10516,f149])).

fof(f10516,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | ~ spl14_285 ),
    inference(subsumption_resolution,[],[f10515,f1723])).

fof(f10515,plain,
    ( ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_80
    | ~ spl14_114
    | ~ spl14_285 ),
    inference(subsumption_resolution,[],[f10514,f1711])).

fof(f10514,plain,
    ( ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_114
    | ~ spl14_285 ),
    inference(subsumption_resolution,[],[f10513,f2551])).

fof(f10513,plain,
    ( ~ m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_285 ),
    inference(subsumption_resolution,[],[f10501,f156])).

fof(f10501,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_285 ),
    inference(resolution,[],[f10413,f190])).

fof(f190,plain,
    ( ! [X4,X5,X3] :
        ( r1_orders_2(sK0,X4,sK6(sK0,X4,X3,X5))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X5)
        | ~ r1_orders_2(sK0,X3,X5)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | sP7(k10_lattice3(sK0,X4,X3),X3,X4,sK0) )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f189,f114])).

fof(f189,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X5)
        | ~ r1_orders_2(sK0,X3,X5)
        | r1_orders_2(sK0,X4,sK6(sK0,X4,X3,X5))
        | ~ l1_orders_2(sK0)
        | sP7(k10_lattice3(sK0,X4,X3),X3,X4,sK0) )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f185,f107])).

fof(f185,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X5)
        | ~ r1_orders_2(sK0,X3,X5)
        | r1_orders_2(sK0,X4,sK6(sK0,X4,X3,X5))
        | ~ l1_orders_2(sK0)
        | sP7(k10_lattice3(sK0,X4,X3),X3,X4,sK0) )
    | ~ spl14_2 ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X4,X5)
        | ~ r1_orders_2(sK0,X3,X5)
        | r1_orders_2(sK0,X4,sK6(sK0,X4,X3,X5))
        | ~ l1_orders_2(sK0)
        | sP7(k10_lattice3(sK0,X4,X3),X3,X4,sK0) )
    | ~ spl14_2 ),
    inference(resolution,[],[f129,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
      | ~ l1_orders_2(X0)
      | sP7(k10_lattice3(X0,X1,X2),X2,X1,X0) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,sK6(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | sP7(X5,X2,X1,X0)
      | k10_lattice3(X0,X1,X2) != X5 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f129,plain,
    ( ! [X37,X38] :
        ( m1_subset_1(k10_lattice3(sK0,X37,X38),u1_struct_0(sK0))
        | ~ m1_subset_1(X38,u1_struct_0(sK0))
        | ~ m1_subset_1(X37,u1_struct_0(sK0)) )
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/yellow_0__t18_yellow_0.p',dt_k10_lattice3)).

fof(f10413,plain,
    ( ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ spl14_285 ),
    inference(avatar_component_clause,[],[f10412])).

fof(f10412,plain,
    ( spl14_285
  <=> ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_285])])).

fof(f10446,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_14
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | spl14_121
    | spl14_283 ),
    inference(avatar_contradiction_clause,[],[f10445])).

fof(f10445,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_14
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | ~ spl14_121
    | ~ spl14_283 ),
    inference(subsumption_resolution,[],[f10444,f2666])).

fof(f10444,plain,
    ( sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_14
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | ~ spl14_283 ),
    inference(forward_demodulation,[],[f10443,f177])).

fof(f10443,plain,
    ( sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | ~ spl14_283 ),
    inference(subsumption_resolution,[],[f10442,f149])).

fof(f10442,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | ~ spl14_283 ),
    inference(subsumption_resolution,[],[f10441,f1723])).

fof(f10441,plain,
    ( ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_80
    | ~ spl14_114
    | ~ spl14_283 ),
    inference(subsumption_resolution,[],[f10440,f1711])).

fof(f10440,plain,
    ( ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_114
    | ~ spl14_283 ),
    inference(subsumption_resolution,[],[f10439,f2551])).

fof(f10439,plain,
    ( ~ m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_283 ),
    inference(subsumption_resolution,[],[f10427,f156])).

fof(f10427,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_283 ),
    inference(resolution,[],[f10407,f192])).

fof(f192,plain,
    ( ! [X6,X8,X7] :
        ( r1_orders_2(sK0,X6,sK6(sK0,X7,X6,X8))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X7,X8)
        | ~ r1_orders_2(sK0,X6,X8)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | sP7(k10_lattice3(sK0,X7,X6),X6,X7,sK0) )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f191,f114])).

fof(f191,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X7,X8)
        | ~ r1_orders_2(sK0,X6,X8)
        | r1_orders_2(sK0,X6,sK6(sK0,X7,X6,X8))
        | ~ l1_orders_2(sK0)
        | sP7(k10_lattice3(sK0,X7,X6),X6,X7,sK0) )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f184,f107])).

fof(f184,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X7,X8)
        | ~ r1_orders_2(sK0,X6,X8)
        | r1_orders_2(sK0,X6,sK6(sK0,X7,X6,X8))
        | ~ l1_orders_2(sK0)
        | sP7(k10_lattice3(sK0,X7,X6),X6,X7,sK0) )
    | ~ spl14_2 ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X7,X8)
        | ~ r1_orders_2(sK0,X6,X8)
        | r1_orders_2(sK0,X6,sK6(sK0,X7,X6,X8))
        | ~ l1_orders_2(sK0)
        | sP7(k10_lattice3(sK0,X7,X6),X6,X7,sK0) )
    | ~ spl14_2 ),
    inference(resolution,[],[f129,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
      | ~ l1_orders_2(X0)
      | sP7(k10_lattice3(X0,X1,X2),X2,X1,X0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X2,sK6(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | sP7(X5,X2,X1,X0)
      | k10_lattice3(X0,X1,X2) != X5 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10407,plain,
    ( ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ spl14_283 ),
    inference(avatar_component_clause,[],[f10406])).

fof(f10406,plain,
    ( spl14_283
  <=> ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_283])])).

fof(f10414,plain,
    ( ~ spl14_283
    | ~ spl14_285
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_232
    | spl14_235 ),
    inference(avatar_split_clause,[],[f8122,f8012,f8003,f155,f148,f113,f10412,f10406])).

fof(f8003,plain,
    ( spl14_232
  <=> m1_subset_1(sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_232])])).

fof(f8012,plain,
    ( spl14_235
  <=> ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_235])])).

fof(f8122,plain,
    ( ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_232
    | ~ spl14_235 ),
    inference(subsumption_resolution,[],[f8121,f8004])).

fof(f8004,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0))
    | ~ spl14_232 ),
    inference(avatar_component_clause,[],[f8003])).

fof(f8121,plain,
    ( ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0))
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_235 ),
    inference(subsumption_resolution,[],[f8120,f149])).

fof(f8120,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0))
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_235 ),
    inference(subsumption_resolution,[],[f8119,f156])).

fof(f8119,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ r1_orders_2(sK0,sK2,sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0))
    | ~ spl14_2
    | ~ spl14_235 ),
    inference(resolution,[],[f8013,f123])).

fof(f123,plain,
    ( ! [X26,X24,X25] :
        ( r2_lattice3(sK0,k2_tarski(X25,X26),X24)
        | ~ m1_subset_1(X25,u1_struct_0(sK0))
        | ~ m1_subset_1(X26,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X25,X24)
        | ~ r1_orders_2(sK0,X26,X24)
        | ~ m1_subset_1(X24,u1_struct_0(sK0)) )
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X1)
      | ~ r1_orders_2(X0,X3,X1)
      | r2_lattice3(X0,k2_tarski(X2,X3),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8013,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ spl14_235 ),
    inference(avatar_component_clause,[],[f8012])).

fof(f8024,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_14
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | spl14_121
    | spl14_233 ),
    inference(avatar_contradiction_clause,[],[f8023])).

fof(f8023,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_14
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | ~ spl14_121
    | ~ spl14_233 ),
    inference(subsumption_resolution,[],[f8022,f2666])).

fof(f8022,plain,
    ( sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_14
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | ~ spl14_233 ),
    inference(forward_demodulation,[],[f8021,f177])).

fof(f8021,plain,
    ( sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | ~ spl14_233 ),
    inference(subsumption_resolution,[],[f8020,f149])).

fof(f8020,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_80
    | ~ spl14_84
    | ~ spl14_114
    | ~ spl14_233 ),
    inference(subsumption_resolution,[],[f8019,f1723])).

fof(f8019,plain,
    ( ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_80
    | ~ spl14_114
    | ~ spl14_233 ),
    inference(subsumption_resolution,[],[f8018,f1711])).

fof(f8018,plain,
    ( ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_114
    | ~ spl14_233 ),
    inference(subsumption_resolution,[],[f8017,f2551])).

fof(f8017,plain,
    ( ~ m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_233 ),
    inference(subsumption_resolution,[],[f8015,f156])).

fof(f8015,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sP7(k10_lattice3(sK0,sK1,sK2),sK2,sK1,sK0)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_233 ),
    inference(resolution,[],[f8007,f188])).

fof(f188,plain,
    ( ! [X2,X0,X1] :
        ( m1_subset_1(sK6(sK0,X1,X0,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | sP7(k10_lattice3(sK0,X1,X0),X0,X1,sK0) )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f187,f114])).

fof(f187,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ r1_orders_2(sK0,X0,X2)
        | m1_subset_1(sK6(sK0,X1,X0,X2),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | sP7(k10_lattice3(sK0,X1,X0),X0,X1,sK0) )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f186,f107])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ r1_orders_2(sK0,X0,X2)
        | m1_subset_1(sK6(sK0,X1,X0,X2),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | sP7(k10_lattice3(sK0,X1,X0),X0,X1,sK0) )
    | ~ spl14_2 ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ r1_orders_2(sK0,X0,X2)
        | m1_subset_1(sK6(sK0,X1,X0,X2),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | sP7(k10_lattice3(sK0,X1,X0),X0,X1,sK0) )
    | ~ spl14_2 ),
    inference(resolution,[],[f129,f101])).

fof(f101,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | sP7(k10_lattice3(X0,X1,X2),X2,X1,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | m1_subset_1(sK6(X0,X1,X2,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | sP7(X5,X2,X1,X0)
      | k10_lattice3(X0,X1,X2) != X5 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8007,plain,
    ( ~ m1_subset_1(sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0))
    | ~ spl14_233 ),
    inference(avatar_component_clause,[],[f8006])).

fof(f8006,plain,
    ( spl14_233
  <=> ~ m1_subset_1(sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_233])])).

fof(f8014,plain,
    ( ~ spl14_233
    | ~ spl14_235
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | spl14_83 ),
    inference(avatar_split_clause,[],[f7997,f1719,f168,f113,f106,f8012,f8006])).

fof(f1719,plain,
    ( spl14_83
  <=> ~ r1_orders_2(sK0,sK9(sK0,k2_tarski(sK1,sK2)),sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_83])])).

fof(f7997,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_83 ),
    inference(subsumption_resolution,[],[f1756,f169])).

fof(f1756,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ m1_subset_1(sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))),u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_83 ),
    inference(resolution,[],[f1720,f135])).

fof(f135,plain,
    ( ! [X35,X34] :
        ( r1_orders_2(sK0,sK9(sK0,X35),X34)
        | ~ r2_lattice3(sK0,X35,X34)
        | ~ m1_subset_1(X34,u1_struct_0(sK0))
        | ~ r1_yellow_0(sK0,X35) )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f127,f107])).

fof(f127,plain,
    ( ! [X35,X34] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X34,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X35,X34)
        | r1_orders_2(sK0,sK9(sK0,X35),X34)
        | ~ r1_yellow_0(sK0,X35) )
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f84])).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,sK9(X0,X1),X3)
      | ~ r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f1720,plain,
    ( ~ r1_orders_2(sK0,sK9(sK0,k2_tarski(sK1,sK2)),sK6(sK0,sK1,sK2,sK9(sK0,k2_tarski(sK1,sK2))))
    | ~ spl14_83 ),
    inference(avatar_component_clause,[],[f1719])).

fof(f3145,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_12
    | spl14_85
    | ~ spl14_114 ),
    inference(avatar_contradiction_clause,[],[f3144])).

fof(f3144,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_12
    | ~ spl14_85
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f3143,f169])).

fof(f3143,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_85
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f3139,f156])).

fof(f3139,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_85
    | ~ spl14_114 ),
    inference(resolution,[],[f3137,f136])).

fof(f3137,plain,
    ( ! [X2] :
        ( ~ r2_lattice3(sK0,k2_tarski(X2,sK2),sK9(sK0,k2_tarski(sK1,sK2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_85
    | ~ spl14_114 ),
    inference(subsumption_resolution,[],[f1754,f2551])).

fof(f1754,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_tarski(X2,sK2),sK9(sK0,k2_tarski(sK1,sK2)))
        | ~ m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0)) )
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_85 ),
    inference(subsumption_resolution,[],[f1744,f149])).

fof(f1744,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k2_tarski(X2,sK2),sK9(sK0,k2_tarski(sK1,sK2)))
        | ~ m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0)) )
    | ~ spl14_2
    | ~ spl14_85 ),
    inference(resolution,[],[f1726,f120])).

fof(f1726,plain,
    ( ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2)))
    | ~ spl14_85 ),
    inference(avatar_component_clause,[],[f1725])).

fof(f1725,plain,
    ( spl14_85
  <=> ~ r1_orders_2(sK0,sK2,sK9(sK0,k2_tarski(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_85])])).

fof(f2929,plain,
    ( ~ spl14_32
    | ~ spl14_40
    | spl14_121
    | spl14_129 ),
    inference(avatar_contradiction_clause,[],[f2928])).

fof(f2928,plain,
    ( $false
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_121
    | ~ spl14_129 ),
    inference(subsumption_resolution,[],[f2927,f2666])).

fof(f2927,plain,
    ( sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_129 ),
    inference(subsumption_resolution,[],[f2926,f449])).

fof(f2926,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_40
    | ~ spl14_129 ),
    inference(subsumption_resolution,[],[f2925,f507])).

fof(f2925,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK1,sK3)
    | sP7(sK3,sK2,sK1,sK0)
    | ~ spl14_129 ),
    inference(resolution,[],[f2920,f61])).

fof(f61,plain,(
    ! [X2,X0,X5,X1] :
      ( m1_subset_1(sK8(X0,X1,X2,X5),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | sP7(X5,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2920,plain,
    ( ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3),u1_struct_0(sK0))
    | ~ spl14_129 ),
    inference(avatar_component_clause,[],[f2919])).

fof(f2919,plain,
    ( spl14_129
  <=> ~ m1_subset_1(sK8(sK0,sK1,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_129])])).

fof(f2887,plain,
    ( ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_40
    | spl14_103 ),
    inference(avatar_contradiction_clause,[],[f2886])).

fof(f2886,plain,
    ( $false
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_103 ),
    inference(subsumption_resolution,[],[f2885,f507])).

fof(f2885,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_32
    | ~ spl14_103 ),
    inference(subsumption_resolution,[],[f2581,f449])).

fof(f2581,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_103 ),
    inference(subsumption_resolution,[],[f2580,f142])).

fof(f2580,plain,
    ( ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_103 ),
    inference(subsumption_resolution,[],[f2579,f149])).

fof(f2579,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_103 ),
    inference(subsumption_resolution,[],[f2199,f156])).

fof(f2199,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl14_2
    | ~ spl14_103 ),
    inference(resolution,[],[f2194,f123])).

fof(f2194,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK3)
    | ~ spl14_103 ),
    inference(avatar_component_clause,[],[f2193])).

fof(f2193,plain,
    ( spl14_103
  <=> ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_103])])).

fof(f2725,plain,
    ( spl14_126
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | spl14_13
    | ~ spl14_32
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f2654,f506,f448,f165,f155,f148,f141,f113,f106,f2723])).

fof(f2654,plain,
    ( r2_lattice3(sK0,k2_tarski(sK1,sK2),sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_13
    | ~ spl14_32
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f2653,f507])).

fof(f2653,plain,
    ( r2_lattice3(sK0,k2_tarski(sK1,sK2),sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_13
    | ~ spl14_32 ),
    inference(subsumption_resolution,[],[f2646,f449])).

fof(f2646,plain,
    ( r2_lattice3(sK0,k2_tarski(sK1,sK2),sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_13 ),
    inference(resolution,[],[f2622,f142])).

fof(f2622,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_lattice3(sK0,k2_tarski(sK1,sK2),sK10(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_13 ),
    inference(subsumption_resolution,[],[f2621,f149])).

fof(f2621,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k2_tarski(sK1,sK2),sK10(sK0,k2_tarski(sK1,sK2),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_13 ),
    inference(subsumption_resolution,[],[f2620,f156])).

fof(f2620,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k2_tarski(sK1,sK2),sK10(sK0,k2_tarski(sK1,sK2),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_13 ),
    inference(duplicate_literal_removal,[],[f2618])).

fof(f2618,plain,
    ( ! [X0] :
        ( r2_lattice3(sK0,k2_tarski(sK1,sK2),sK10(sK0,k2_tarski(sK1,sK2),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_13 ),
    inference(resolution,[],[f2610,f123])).

fof(f2610,plain,
    ( ! [X5] :
        ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X5)
        | r2_lattice3(sK0,k2_tarski(sK1,sK2),sK10(sK0,k2_tarski(sK1,sK2),X5))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_13 ),
    inference(resolution,[],[f166,f133])).

fof(f133,plain,
    ( ! [X30,X31] :
        ( r1_yellow_0(sK0,X31)
        | ~ r2_lattice3(sK0,X31,X30)
        | r2_lattice3(sK0,X31,sK10(sK0,X31,X30))
        | ~ m1_subset_1(X30,u1_struct_0(sK0)) )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f125,f107])).

fof(f125,plain,
    ( ! [X30,X31] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X30,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X31,X30)
        | r2_lattice3(sK0,X31,sK10(sK0,X31,X30))
        | r1_yellow_0(sK0,X31) )
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,X1,sK10(X0,X1,X2))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2704,plain,
    ( ~ spl14_125
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | spl14_13
    | ~ spl14_32
    | ~ spl14_40 ),
    inference(avatar_split_clause,[],[f2636,f506,f448,f165,f155,f148,f141,f113,f106,f2702])).

fof(f2636,plain,
    ( ~ r1_orders_2(sK0,sK3,sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_13
    | ~ spl14_32
    | ~ spl14_40 ),
    inference(subsumption_resolution,[],[f2635,f507])).

fof(f2635,plain,
    ( ~ r1_orders_2(sK0,sK3,sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_13
    | ~ spl14_32 ),
    inference(subsumption_resolution,[],[f2628,f449])).

fof(f2628,plain,
    ( ~ r1_orders_2(sK0,sK3,sK10(sK0,k2_tarski(sK1,sK2),sK3))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ r1_orders_2(sK0,sK2,sK3)
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_4
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_13 ),
    inference(resolution,[],[f2615,f142])).

fof(f2615,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,sK10(sK0,k2_tarski(sK1,sK2),X0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_13 ),
    inference(subsumption_resolution,[],[f2614,f149])).

fof(f2614,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK10(sK0,k2_tarski(sK1,sK2),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_13 ),
    inference(subsumption_resolution,[],[f2613,f156])).

fof(f2613,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK10(sK0,k2_tarski(sK1,sK2),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_13 ),
    inference(duplicate_literal_removal,[],[f2611])).

fof(f2611,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,X0,sK10(sK0,k2_tarski(sK1,sK2),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X0)
        | ~ r1_orders_2(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_13 ),
    inference(resolution,[],[f2609,f123])).

fof(f2609,plain,
    ( ! [X4] :
        ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),X4)
        | ~ r1_orders_2(sK0,X4,sK10(sK0,k2_tarski(sK1,sK2),X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_13 ),
    inference(resolution,[],[f166,f134])).

fof(f134,plain,
    ( ! [X33,X32] :
        ( r1_yellow_0(sK0,X33)
        | ~ r2_lattice3(sK0,X33,X32)
        | ~ r1_orders_2(sK0,X32,sK10(sK0,X33,X32))
        | ~ m1_subset_1(X32,u1_struct_0(sK0)) )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f126,f107])).

fof(f126,plain,
    ( ! [X33,X32] :
        ( ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X32,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X33,X32)
        | ~ r1_orders_2(sK0,X32,sK10(sK0,X33,X32))
        | r1_yellow_0(sK0,X33) )
    | ~ spl14_2 ),
    inference(resolution,[],[f114,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,sK10(X0,X1,X2))
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f2683,plain,
    ( ~ spl14_123
    | ~ spl14_32
    | ~ spl14_40
    | spl14_121 ),
    inference(avatar_split_clause,[],[f2676,f2665,f506,f448,f2681])).

fof(f2676,plain,
    ( ~ r1_orders_2(sK0,sK3,sK8(sK0,sK1,sK2,sK3))
    | ~ spl14_32
    | ~ spl14_40
    | ~ spl14_121 ),
    inference(subsumption_resolution,[],[f2675,f449])).

fof(f2675,plain,
    ( ~ r1_orders_2(sK0,sK3,sK8(sK0,sK1,sK2,sK3))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ spl14_40
    | ~ spl14_121 ),
    inference(subsumption_resolution,[],[f2672,f507])).

fof(f2672,plain,
    ( ~ r1_orders_2(sK0,sK2,sK3)
    | ~ r1_orders_2(sK0,sK3,sK8(sK0,sK1,sK2,sK3))
    | ~ r1_orders_2(sK0,sK1,sK3)
    | ~ spl14_121 ),
    inference(resolution,[],[f2666,f64])).

fof(f64,plain,(
    ! [X2,X0,X5,X1] :
      ( sP7(X5,X2,X1,X0)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X5,sK8(X0,X1,X2,X5))
      | ~ r1_orders_2(X0,X1,X5) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2670,plain,
    ( spl14_118
    | spl14_120
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_14 ),
    inference(avatar_split_clause,[],[f845,f176,f155,f148,f113,f106,f2668,f2662])).

fof(f845,plain,
    ( ! [X4] :
        ( sP7(sK3,sK2,sK1,sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X4)
        | ~ r1_orders_2(sK0,sK2,X4)
        | ~ r1_orders_2(sK0,X4,sK6(sK0,sK1,sK2,X4)) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_6
    | ~ spl14_8
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f844,f149])).

fof(f844,plain,
    ( ! [X4] :
        ( sP7(sK3,sK2,sK1,sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X4)
        | ~ r1_orders_2(sK0,sK2,X4)
        | ~ r1_orders_2(sK0,X4,sK6(sK0,sK1,sK2,X4))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_8
    | ~ spl14_14 ),
    inference(subsumption_resolution,[],[f835,f156])).

fof(f835,plain,
    ( ! [X4] :
        ( sP7(sK3,sK2,sK1,sK0)
        | ~ m1_subset_1(sK1,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK1,X4)
        | ~ r1_orders_2(sK0,sK2,X4)
        | ~ r1_orders_2(sK0,X4,sK6(sK0,sK1,sK2,X4))
        | ~ m1_subset_1(sK2,u1_struct_0(sK0)) )
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_14 ),
    inference(superposition,[],[f194,f177])).

fof(f194,plain,
    ( ! [X10,X11,X9] :
        ( sP7(k10_lattice3(sK0,X10,X9),X9,X10,sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X11)
        | ~ r1_orders_2(sK0,X9,X11)
        | ~ r1_orders_2(sK0,X11,sK6(sK0,X10,X9,X11))
        | ~ m1_subset_1(X9,u1_struct_0(sK0)) )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f193,f114])).

fof(f193,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X11)
        | ~ r1_orders_2(sK0,X9,X11)
        | ~ r1_orders_2(sK0,X11,sK6(sK0,X10,X9,X11))
        | ~ l1_orders_2(sK0)
        | sP7(k10_lattice3(sK0,X10,X9),X9,X10,sK0) )
    | ~ spl14_0
    | ~ spl14_2 ),
    inference(subsumption_resolution,[],[f183,f107])).

fof(f183,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X11)
        | ~ r1_orders_2(sK0,X9,X11)
        | ~ r1_orders_2(sK0,X11,sK6(sK0,X10,X9,X11))
        | ~ l1_orders_2(sK0)
        | sP7(k10_lattice3(sK0,X10,X9),X9,X10,sK0) )
    | ~ spl14_2 ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,
    ( ! [X10,X11,X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X11,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X10,X11)
        | ~ r1_orders_2(sK0,X9,X11)
        | ~ r1_orders_2(sK0,X11,sK6(sK0,X10,X9,X11))
        | ~ l1_orders_2(sK0)
        | sP7(k10_lattice3(sK0,X10,X9),X9,X10,sK0) )
    | ~ spl14_2 ),
    inference(resolution,[],[f129,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(k10_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
      | ~ l1_orders_2(X0)
      | sP7(k10_lattice3(X0,X1,X2),X2,X1,X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X3,sK6(X0,X1,X2,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | sP7(X5,X2,X1,X0)
      | k10_lattice3(X0,X1,X2) != X5 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2571,plain,
    ( ~ spl14_10
    | spl14_41 ),
    inference(avatar_contradiction_clause,[],[f2570])).

fof(f2570,plain,
    ( $false
    | ~ spl14_10
    | ~ spl14_41 ),
    inference(subsumption_resolution,[],[f163,f520])).

fof(f520,plain,
    ( ! [X6] : ~ sP4(sK3,sK2,X6,sK0)
    | ~ spl14_41 ),
    inference(resolution,[],[f510,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | ~ sP4(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2568,plain,
    ( ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | spl14_115 ),
    inference(avatar_contradiction_clause,[],[f2567])).

fof(f2567,plain,
    ( $false
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_12
    | ~ spl14_115 ),
    inference(subsumption_resolution,[],[f2566,f169])).

fof(f2566,plain,
    ( ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_0
    | ~ spl14_2
    | ~ spl14_115 ),
    inference(subsumption_resolution,[],[f2565,f107])).

fof(f2565,plain,
    ( ~ v5_orders_2(sK0)
    | ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_2
    | ~ spl14_115 ),
    inference(subsumption_resolution,[],[f2564,f114])).

fof(f2564,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl14_115 ),
    inference(resolution,[],[f2554,f85])).

fof(f2554,plain,
    ( ~ m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0))
    | ~ spl14_115 ),
    inference(avatar_component_clause,[],[f2553])).

fof(f2553,plain,
    ( spl14_115
  <=> ~ m1_subset_1(sK9(sK0,k2_tarski(sK1,sK2)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_115])])).

fof(f832,plain,
    ( ~ spl14_10
    | spl14_33 ),
    inference(avatar_contradiction_clause,[],[f831])).

fof(f831,plain,
    ( $false
    | ~ spl14_10
    | ~ spl14_33 ),
    inference(resolution,[],[f463,f163])).

fof(f463,plain,
    ( ! [X7] : ~ sP4(sK3,X7,sK1,sK0)
    | ~ spl14_33 ),
    inference(resolution,[],[f452,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | ~ sP4(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f178,plain,
    ( spl14_14
    | spl14_11 ),
    inference(avatar_split_clause,[],[f171,f159,f176])).

fof(f171,plain,
    ( k10_lattice3(sK0,sK1,sK2) = sK3
    | ~ spl14_11 ),
    inference(subsumption_resolution,[],[f51,f160])).

fof(f51,plain,
    ( k10_lattice3(sK0,sK1,sK2) = sK3
    | sP4(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f170,plain,
    ( spl14_10
    | spl14_12 ),
    inference(avatar_split_clause,[],[f52,f168,f162])).

fof(f52,plain,
    ( r1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | sP4(sK3,sK2,sK1,sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f157,plain,(
    spl14_8 ),
    inference(avatar_split_clause,[],[f55,f155])).

fof(f55,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f150,plain,(
    spl14_6 ),
    inference(avatar_split_clause,[],[f54,f148])).

fof(f54,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f143,plain,(
    spl14_4 ),
    inference(avatar_split_clause,[],[f53,f141])).

fof(f53,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f115,plain,(
    spl14_2 ),
    inference(avatar_split_clause,[],[f57,f113])).

fof(f57,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).

fof(f108,plain,(
    spl14_0 ),
    inference(avatar_split_clause,[],[f56,f106])).

fof(f56,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
