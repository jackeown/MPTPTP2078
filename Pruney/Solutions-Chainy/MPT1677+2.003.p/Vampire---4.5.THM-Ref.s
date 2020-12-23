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
% DateTime   : Thu Dec  3 13:17:18 EST 2020

% Result     : Theorem 1.71s
% Output     : Refutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 367 expanded)
%              Number of leaves         :   28 ( 118 expanded)
%              Depth                    :   22
%              Number of atoms          :  806 (2239 expanded)
%              Number of equality atoms :   34 ( 178 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1466,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f106,f129,f608,f629,f645,f923,f940,f1020,f1023,f1090,f1095,f1149,f1160,f1352,f1442,f1463])).

fof(f1463,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_35 ),
    inference(avatar_contradiction_clause,[],[f1462])).

fof(f1462,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1461,f127])).

fof(f127,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl7_9
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1461,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f1454,f105])).

fof(f105,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f1454,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_35 ),
    inference(resolution,[],[f1351,f100])).

fof(f100,plain,
    ( ! [X24,X23] :
        ( ~ r1_orders_2(sK0,X23,sK6(sK0,X24,X23))
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | r1_lattice3(sK0,X24,X23) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).

fof(f86,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl7_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1351,plain,
    ( r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f1349])).

fof(f1349,plain,
    ( spl7_35
  <=> r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f1442,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_23
    | ~ spl7_27
    | spl7_34 ),
    inference(avatar_contradiction_clause,[],[f1441])).

fof(f1441,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_23
    | ~ spl7_27
    | spl7_34 ),
    inference(subsumption_resolution,[],[f1440,f1088])).

fof(f1088,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f1087])).

fof(f1087,plain,
    ( spl7_23
  <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f1440,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | ~ spl7_27
    | spl7_34 ),
    inference(subsumption_resolution,[],[f1439,f1147])).

fof(f1147,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f1146])).

fof(f1146,plain,
    ( spl7_27
  <=> r2_hidden(sK6(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f1439,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_8
    | spl7_34 ),
    inference(subsumption_resolution,[],[f1438,f124])).

fof(f124,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl7_8
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f1438,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_4
    | ~ spl7_5
    | spl7_34 ),
    inference(resolution,[],[f1410,f28])).

fof(f28,plain,(
    ! [X4] :
      ( m1_subset_1(sK4(X4),k1_zfmisc_1(sK1))
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <~> r1_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r1_lattice3(X0,X1,X7)
                  <~> r1_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k2_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k2_yellow_0(X0,X5) = X4
                      & r2_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r2_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k2_yellow_0(X0,X5) = X4
                                    & r2_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r2_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X1,X7)
                      <=> r1_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k2_yellow_0(X0,X4) = X3
                                    & r2_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r2_yellow_0(X0,X3) ) ) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r1_lattice3(X0,X1,X3)
                      <=> r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_hidden(k2_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k2_yellow_0(X0,X4) = X3
                                  & r2_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r2_yellow_0(X0,X3) ) ) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                    <=> r1_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_waybel_0)).

fof(f1410,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(X0))
        | ~ r1_lattice3(sK0,X0,sK3) )
    | ~ spl7_4
    | ~ spl7_5
    | spl7_34 ),
    inference(resolution,[],[f1365,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1365,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X1)
        | ~ r1_lattice3(sK0,X1,sK3) )
    | ~ spl7_4
    | ~ spl7_5
    | spl7_34 ),
    inference(subsumption_resolution,[],[f1363,f105])).

fof(f1363,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X1,sK3)
        | ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X1) )
    | ~ spl7_4
    | spl7_34 ),
    inference(resolution,[],[f1347,f95])).

fof(f95,plain,
    ( ! [X12,X13,X11] :
        ( r1_lattice3(sK0,X11,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X12,X13)
        | ~ r1_tarski(X11,X12) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ! [X3] :
              ( ( ( r2_lattice3(X0,X1,X3)
                  | ~ r2_lattice3(X0,X2,X3) )
                & ( r1_lattice3(X0,X1,X3)
                  | ~ r1_lattice3(X0,X2,X3) ) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ r1_tarski(X1,X2) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( r1_tarski(X1,X2)
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r2_lattice3(X0,X2,X3)
                 => r2_lattice3(X0,X1,X3) )
                & ( r1_lattice3(X0,X2,X3)
                 => r1_lattice3(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f1347,plain,
    ( ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | spl7_34 ),
    inference(avatar_component_clause,[],[f1345])).

fof(f1345,plain,
    ( spl7_34
  <=> r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f1352,plain,
    ( ~ spl7_34
    | spl7_35
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_22
    | ~ spl7_25 ),
    inference(avatar_split_clause,[],[f1278,f1134,f1083,f103,f84,f1349,f1345])).

fof(f1083,plain,
    ( spl7_22
  <=> sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f1134,plain,
    ( spl7_25
  <=> r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f1278,plain,
    ( r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))
    | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_22
    | ~ spl7_25 ),
    inference(resolution,[],[f1275,f105])).

fof(f1275,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_orders_2(sK0,X2,sK6(sK0,sK2,sK3))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X2) )
    | ~ spl7_4
    | ~ spl7_22
    | ~ spl7_25 ),
    inference(subsumption_resolution,[],[f1111,f1135])).

fof(f1135,plain,
    ( r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_25 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f1111,plain,
    ( ! [X2] :
        ( r1_orders_2(sK0,X2,sK6(sK0,sK2,sK3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X2)
        | ~ r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) )
    | ~ spl7_4
    | ~ spl7_22 ),
    inference(superposition,[],[f119,f1085])).

fof(f1085,plain,
    ( sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f1083])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ r2_yellow_0(sK0,X0) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f117,f86])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f101,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f101,plain,
    ( ! [X25] : m1_subset_1(k2_yellow_0(sK0,X25),u1_struct_0(sK0))
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).

fof(f1160,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | spl7_27 ),
    inference(avatar_contradiction_clause,[],[f1159])).

fof(f1159,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | spl7_27 ),
    inference(subsumption_resolution,[],[f1158,f127])).

fof(f1158,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_27 ),
    inference(subsumption_resolution,[],[f1157,f105])).

fof(f1157,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | spl7_27 ),
    inference(resolution,[],[f1148,f99])).

fof(f99,plain,
    ( ! [X21,X22] :
        ( r2_hidden(sK6(sK0,X22,X21),X22)
        | ~ m1_subset_1(X21,u1_struct_0(sK0))
        | r1_lattice3(sK0,X22,X21) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1148,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | spl7_27 ),
    inference(avatar_component_clause,[],[f1146])).

fof(f1149,plain,
    ( ~ spl7_27
    | ~ spl7_23
    | spl7_25 ),
    inference(avatar_split_clause,[],[f1144,f1134,f1087,f1146])).

fof(f1144,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl7_23
    | spl7_25 ),
    inference(subsumption_resolution,[],[f1142,f1088])).

fof(f1142,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_25 ),
    inference(resolution,[],[f1136,f29])).

fof(f29,plain,(
    ! [X4] :
      ( r2_yellow_0(sK0,sK4(X4))
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1136,plain,
    ( ~ r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f1134])).

fof(f1095,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | spl7_23 ),
    inference(avatar_contradiction_clause,[],[f1094])).

fof(f1094,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | spl7_23 ),
    inference(subsumption_resolution,[],[f1093,f127])).

fof(f1093,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_23 ),
    inference(subsumption_resolution,[],[f1092,f86])).

fof(f1092,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_5
    | spl7_23 ),
    inference(subsumption_resolution,[],[f1091,f105])).

fof(f1091,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK3)
    | spl7_23 ),
    inference(resolution,[],[f1089,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1089,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_23 ),
    inference(avatar_component_clause,[],[f1087])).

fof(f1090,plain,
    ( spl7_22
    | ~ spl7_23
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(avatar_split_clause,[],[f1032,f126,f103,f84,f1087,f1083])).

fof(f1032,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(subsumption_resolution,[],[f1025,f105])).

fof(f1025,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_4
    | spl7_9 ),
    inference(resolution,[],[f127,f132])).

fof(f132,plain,
    ( ! [X0] :
        ( r1_lattice3(sK0,sK2,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK2,X0),u1_struct_0(sK0))
        | sK6(sK0,sK2,X0) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,X0))) )
    | ~ spl7_4 ),
    inference(resolution,[],[f99,f30])).

fof(f30,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_yellow_0(sK0,sK4(X4)) = X4 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1023,plain,
    ( ~ spl7_8
    | ~ spl7_9 ),
    inference(avatar_contradiction_clause,[],[f1022])).

fof(f1022,plain,
    ( $false
    | ~ spl7_8
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f1021,f124])).

fof(f1021,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_9 ),
    inference(subsumption_resolution,[],[f32,f128])).

fof(f128,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f32,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f1020,plain,(
    ~ spl7_12 ),
    inference(avatar_contradiction_clause,[],[f1019])).

fof(f1019,plain,
    ( $false
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f975,f42])).

fof(f42,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f975,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_12 ),
    inference(superposition,[],[f43,f440])).

fof(f440,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl7_12
  <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f43,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f940,plain,
    ( spl7_12
    | ~ spl7_16
    | spl7_20 ),
    inference(avatar_contradiction_clause,[],[f939])).

fof(f939,plain,
    ( $false
    | spl7_12
    | ~ spl7_16
    | spl7_20 ),
    inference(subsumption_resolution,[],[f938,f44])).

fof(f44,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f938,plain,
    ( ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_12
    | ~ spl7_16
    | spl7_20 ),
    inference(subsumption_resolution,[],[f937,f439])).

fof(f439,plain,
    ( k1_xboole_0 != k1_tarski(sK6(sK0,sK1,sK3))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f438])).

fof(f937,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_16
    | spl7_20 ),
    inference(subsumption_resolution,[],[f936,f606])).

fof(f606,plain,
    ( m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f605])).

fof(f605,plain,
    ( spl7_16
  <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f936,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_20 ),
    inference(resolution,[],[f922,f35])).

fof(f35,plain,(
    ! [X6] :
      ( r2_yellow_0(sK0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
      | k1_xboole_0 = X6
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f922,plain,
    ( ~ r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_20 ),
    inference(avatar_component_clause,[],[f920])).

fof(f920,plain,
    ( spl7_20
  <=> r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f923,plain,
    ( ~ spl7_20
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_8
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f904,f593,f126,f122,f103,f84,f79,f920])).

fof(f79,plain,
    ( spl7_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f593,plain,
    ( spl7_15
  <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f904,plain,
    ( ~ r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_8
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f899,f123])).

fof(f123,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | spl7_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f899,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(resolution,[],[f735,f120])).

fof(f120,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2))
        | ~ r2_yellow_0(sK0,X2) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f118,f86])).

fof(f118,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f101,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f735,plain,
    ( ! [X4] :
        ( ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X4,sK3)),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
        | r1_lattice3(sK0,X4,sK3) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f734,f128])).

fof(f734,plain,
    ( ! [X4] :
        ( r1_lattice3(sK0,X4,sK3)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X4,sK3)),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
        | ~ r1_lattice3(sK0,sK2,sK3) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(subsumption_resolution,[],[f709,f101])).

fof(f709,plain,
    ( ! [X4] :
        ( r1_lattice3(sK0,X4,sK3)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X4,sK3)),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
        | ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK2,sK3) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_15 ),
    inference(resolution,[],[f594,f361])).

fof(f361,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,X2)
        | r1_lattice3(sK0,X1,sK3)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X1,sK3)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X2,sK3) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f360,f105])).

fof(f360,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK3)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X1,sK3)),X0)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X2,sK3) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f354])).

fof(f354,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,sK3)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X1,sK3)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X2,sK3) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f301,f98])).

fof(f98,plain,
    ( ! [X19,X20,X18] :
        ( r1_orders_2(sK0,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | ~ r2_hidden(X19,X20)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X20,X18) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f301,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,sK3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,sK3)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,sK3)),X1) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(resolution,[],[f212,f105])).

fof(f212,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattice3(sK0,X3,X2)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X4)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X3,X2)),X4) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f209])).

fof(f209,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattice3(sK0,X3,X2)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X4)
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X3,X2)),X4)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f195,f157])).

fof(f157,plain,
    ( ! [X4,X5,X3] :
        ( r1_lattice3(sK0,X5,X3)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X4)
        | ~ r1_lattice3(sK0,X5,X4)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f89,f86])).

fof(f89,plain,
    ( ! [X4,X5,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X3,X4)
        | ~ r1_lattice3(sK0,X5,X4)
        | r1_lattice3(sK0,X5,X3) )
    | ~ spl7_3 ),
    inference(resolution,[],[f81,f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_lattice3(X0,X3,X2)
      | r1_lattice3(X0,X3,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_lattice3(X0,X3,X2)
                    | ~ r2_lattice3(X0,X3,X1) )
                  & ( r1_lattice3(X0,X3,X1)
                    | ~ r1_lattice3(X0,X3,X2) ) )
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
               => ! [X3] :
                    ( ( r2_lattice3(X0,X3,X1)
                     => r2_lattice3(X0,X3,X2) )
                    & ( r1_lattice3(X0,X3,X2)
                     => r1_lattice3(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).

fof(f81,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f195,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f194,f86])).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f146,f57])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f93,f100])).

fof(f93,plain,
    ( ! [X6,X7] :
        ( r1_orders_2(sK0,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(X7),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X2,X1)
                  | ~ r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                  | ~ r1_orders_2(X0,X1,X2) )
                & ( r1_orders_2(X0,X1,X2)
                  | ~ r1_lattice3(X0,k1_tarski(X2),X1) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X1)
                 => r2_lattice3(X0,k1_tarski(X2),X1) )
                & ( r2_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X2,X1) )
                & ( r1_orders_2(X0,X1,X2)
                 => r1_lattice3(X0,k1_tarski(X2),X1) )
                & ( r1_lattice3(X0,k1_tarski(X2),X1)
                 => r1_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).

fof(f594,plain,
    ( r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f593])).

fof(f645,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | spl7_8
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f644])).

fof(f644,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | spl7_8
    | spl7_17 ),
    inference(subsumption_resolution,[],[f643,f123])).

fof(f643,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_17 ),
    inference(subsumption_resolution,[],[f642,f105])).

fof(f642,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_4
    | spl7_17 ),
    inference(resolution,[],[f628,f99])).

fof(f628,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | spl7_17 ),
    inference(avatar_component_clause,[],[f626])).

fof(f626,plain,
    ( spl7_17
  <=> r2_hidden(sK6(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f629,plain,
    ( ~ spl7_17
    | spl7_16 ),
    inference(avatar_split_clause,[],[f620,f605,f626])).

fof(f620,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | spl7_16 ),
    inference(resolution,[],[f607,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f607,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | spl7_16 ),
    inference(avatar_component_clause,[],[f605])).

fof(f608,plain,
    ( ~ spl7_16
    | spl7_12
    | spl7_15 ),
    inference(avatar_split_clause,[],[f599,f593,f438,f605])).

fof(f599,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | spl7_12
    | spl7_15 ),
    inference(subsumption_resolution,[],[f598,f44])).

fof(f598,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_12
    | spl7_15 ),
    inference(subsumption_resolution,[],[f597,f439])).

fof(f597,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_15 ),
    inference(resolution,[],[f595,f34])).

fof(f34,plain,(
    ! [X3] :
      ( r2_hidden(k2_yellow_0(sK0,X3),sK2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | k1_xboole_0 = X3
      | ~ v1_finset_1(X3) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f595,plain,
    ( ~ r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f593])).

fof(f129,plain,
    ( spl7_8
    | spl7_9 ),
    inference(avatar_split_clause,[],[f31,f126,f122])).

fof(f31,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f106,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f33,f103])).

fof(f33,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f87,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f41,f84])).

fof(f41,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:18:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (9994)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (10006)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (9997)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (9998)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (10007)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (10002)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (9999)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (9995)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (10004)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (9996)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (10005)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (10001)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (9992)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (9993)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (10000)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.54  % (10012)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.54  % (10011)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.55  % (10008)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.55  % (10003)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.55  % (10009)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.55  % (10010)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.71/0.63  % (9995)Refutation found. Thanks to Tanya!
% 1.71/0.63  % SZS status Theorem for theBenchmark
% 1.71/0.64  % SZS output start Proof for theBenchmark
% 1.71/0.64  fof(f1466,plain,(
% 1.71/0.64    $false),
% 1.71/0.64    inference(avatar_sat_refutation,[],[f82,f87,f106,f129,f608,f629,f645,f923,f940,f1020,f1023,f1090,f1095,f1149,f1160,f1352,f1442,f1463])).
% 1.71/0.64  fof(f1463,plain,(
% 1.71/0.64    ~spl7_4 | ~spl7_5 | spl7_9 | ~spl7_35),
% 1.71/0.64    inference(avatar_contradiction_clause,[],[f1462])).
% 1.71/0.64  fof(f1462,plain,(
% 1.71/0.64    $false | (~spl7_4 | ~spl7_5 | spl7_9 | ~spl7_35)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1461,f127])).
% 1.71/0.64  fof(f127,plain,(
% 1.71/0.64    ~r1_lattice3(sK0,sK2,sK3) | spl7_9),
% 1.71/0.64    inference(avatar_component_clause,[],[f126])).
% 1.71/0.64  fof(f126,plain,(
% 1.71/0.64    spl7_9 <=> r1_lattice3(sK0,sK2,sK3)),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 1.71/0.64  fof(f1461,plain,(
% 1.71/0.64    r1_lattice3(sK0,sK2,sK3) | (~spl7_4 | ~spl7_5 | ~spl7_35)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1454,f105])).
% 1.71/0.64  fof(f105,plain,(
% 1.71/0.64    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl7_5),
% 1.71/0.64    inference(avatar_component_clause,[],[f103])).
% 1.71/0.64  fof(f103,plain,(
% 1.71/0.64    spl7_5 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 1.71/0.64  fof(f1454,plain,(
% 1.71/0.64    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | (~spl7_4 | ~spl7_35)),
% 1.71/0.64    inference(resolution,[],[f1351,f100])).
% 1.71/0.64  fof(f100,plain,(
% 1.71/0.64    ( ! [X24,X23] : (~r1_orders_2(sK0,X23,sK6(sK0,X24,X23)) | ~m1_subset_1(X23,u1_struct_0(sK0)) | r1_lattice3(sK0,X24,X23)) ) | ~spl7_4),
% 1.71/0.64    inference(resolution,[],[f86,f59])).
% 1.71/0.64  fof(f59,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X2,sK6(X0,X1,X2)) | r1_lattice3(X0,X1,X2)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f22])).
% 1.71/0.64  fof(f22,plain,(
% 1.71/0.64    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.71/0.64    inference(flattening,[],[f21])).
% 1.71/0.64  fof(f21,plain,(
% 1.71/0.64    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.71/0.64    inference(ennf_transformation,[],[f6])).
% 1.71/0.64  fof(f6,axiom,(
% 1.71/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 1.71/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 1.71/0.64  fof(f86,plain,(
% 1.71/0.64    l1_orders_2(sK0) | ~spl7_4),
% 1.71/0.64    inference(avatar_component_clause,[],[f84])).
% 1.71/0.64  fof(f84,plain,(
% 1.71/0.64    spl7_4 <=> l1_orders_2(sK0)),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 1.71/0.64  fof(f1351,plain,(
% 1.71/0.64    r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3)) | ~spl7_35),
% 1.71/0.64    inference(avatar_component_clause,[],[f1349])).
% 1.71/0.64  fof(f1349,plain,(
% 1.71/0.64    spl7_35 <=> r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3))),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 1.71/0.64  fof(f1442,plain,(
% 1.71/0.64    ~spl7_4 | ~spl7_5 | ~spl7_8 | ~spl7_23 | ~spl7_27 | spl7_34),
% 1.71/0.64    inference(avatar_contradiction_clause,[],[f1441])).
% 1.71/0.64  fof(f1441,plain,(
% 1.71/0.64    $false | (~spl7_4 | ~spl7_5 | ~spl7_8 | ~spl7_23 | ~spl7_27 | spl7_34)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1440,f1088])).
% 1.71/0.64  fof(f1088,plain,(
% 1.71/0.64    m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | ~spl7_23),
% 1.71/0.64    inference(avatar_component_clause,[],[f1087])).
% 1.71/0.64  fof(f1087,plain,(
% 1.71/0.64    spl7_23 <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 1.71/0.64  fof(f1440,plain,(
% 1.71/0.64    ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | (~spl7_4 | ~spl7_5 | ~spl7_8 | ~spl7_27 | spl7_34)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1439,f1147])).
% 1.71/0.64  fof(f1147,plain,(
% 1.71/0.64    r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~spl7_27),
% 1.71/0.64    inference(avatar_component_clause,[],[f1146])).
% 1.71/0.64  fof(f1146,plain,(
% 1.71/0.64    spl7_27 <=> r2_hidden(sK6(sK0,sK2,sK3),sK2)),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 1.71/0.64  fof(f1439,plain,(
% 1.71/0.64    ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | (~spl7_4 | ~spl7_5 | ~spl7_8 | spl7_34)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1438,f124])).
% 1.71/0.64  fof(f124,plain,(
% 1.71/0.64    r1_lattice3(sK0,sK1,sK3) | ~spl7_8),
% 1.71/0.64    inference(avatar_component_clause,[],[f122])).
% 1.71/0.64  fof(f122,plain,(
% 1.71/0.64    spl7_8 <=> r1_lattice3(sK0,sK1,sK3)),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 1.71/0.64  fof(f1438,plain,(
% 1.71/0.64    ~r1_lattice3(sK0,sK1,sK3) | ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | (~spl7_4 | ~spl7_5 | spl7_34)),
% 1.71/0.64    inference(resolution,[],[f1410,f28])).
% 1.71/0.64  fof(f28,plain,(
% 1.71/0.64    ( ! [X4] : (m1_subset_1(sK4(X4),k1_zfmisc_1(sK1)) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0))) )),
% 1.71/0.64    inference(cnf_transformation,[],[f16])).
% 1.71/0.64  fof(f16,plain,(
% 1.71/0.64    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.71/0.64    inference(flattening,[],[f15])).
% 1.71/0.64  fof(f15,plain,(
% 1.71/0.64    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r2_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.71/0.64    inference(ennf_transformation,[],[f14])).
% 1.71/0.64  fof(f14,plain,(
% 1.71/0.64    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 1.71/0.64    inference(rectify,[],[f13])).
% 1.71/0.64  fof(f13,negated_conjecture,(
% 1.71/0.64    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 1.71/0.64    inference(negated_conjecture,[],[f12])).
% 1.71/0.64  fof(f12,conjecture,(
% 1.71/0.64    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 1.71/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_waybel_0)).
% 1.71/0.64  fof(f1410,plain,(
% 1.71/0.64    ( ! [X0] : (~m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(X0)) | ~r1_lattice3(sK0,X0,sK3)) ) | (~spl7_4 | ~spl7_5 | spl7_34)),
% 1.71/0.64    inference(resolution,[],[f1365,f65])).
% 1.71/0.64  fof(f65,plain,(
% 1.71/0.64    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.71/0.64    inference(cnf_transformation,[],[f4])).
% 1.71/0.64  fof(f4,axiom,(
% 1.71/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.71/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.71/0.64  fof(f1365,plain,(
% 1.71/0.64    ( ! [X1] : (~r1_tarski(sK4(sK6(sK0,sK2,sK3)),X1) | ~r1_lattice3(sK0,X1,sK3)) ) | (~spl7_4 | ~spl7_5 | spl7_34)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1363,f105])).
% 1.71/0.64  fof(f1363,plain,(
% 1.71/0.64    ( ! [X1] : (~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X1,sK3) | ~r1_tarski(sK4(sK6(sK0,sK2,sK3)),X1)) ) | (~spl7_4 | spl7_34)),
% 1.71/0.64    inference(resolution,[],[f1347,f95])).
% 1.71/0.64  fof(f95,plain,(
% 1.71/0.64    ( ! [X12,X13,X11] : (r1_lattice3(sK0,X11,X13) | ~m1_subset_1(X13,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X12,X13) | ~r1_tarski(X11,X12)) ) | ~spl7_4),
% 1.71/0.64    inference(resolution,[],[f86,f50])).
% 1.71/0.64  fof(f50,plain,(
% 1.71/0.64    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~r1_tarski(X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f18])).
% 1.71/0.64  fof(f18,plain,(
% 1.71/0.64    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 1.71/0.64    inference(ennf_transformation,[],[f11])).
% 1.71/0.64  fof(f11,axiom,(
% 1.71/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 1.71/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_yellow_0)).
% 1.71/0.64  fof(f1347,plain,(
% 1.71/0.64    ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | spl7_34),
% 1.71/0.64    inference(avatar_component_clause,[],[f1345])).
% 1.71/0.64  fof(f1345,plain,(
% 1.71/0.64    spl7_34 <=> r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 1.71/0.64  fof(f1352,plain,(
% 1.71/0.64    ~spl7_34 | spl7_35 | ~spl7_4 | ~spl7_5 | ~spl7_22 | ~spl7_25),
% 1.71/0.64    inference(avatar_split_clause,[],[f1278,f1134,f1083,f103,f84,f1349,f1345])).
% 1.71/0.64  fof(f1083,plain,(
% 1.71/0.64    spl7_22 <=> sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 1.71/0.64  fof(f1134,plain,(
% 1.71/0.64    spl7_25 <=> r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 1.71/0.64  fof(f1278,plain,(
% 1.71/0.64    r1_orders_2(sK0,sK3,sK6(sK0,sK2,sK3)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) | (~spl7_4 | ~spl7_5 | ~spl7_22 | ~spl7_25)),
% 1.71/0.64    inference(resolution,[],[f1275,f105])).
% 1.71/0.64  fof(f1275,plain,(
% 1.71/0.64    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_orders_2(sK0,X2,sK6(sK0,sK2,sK3)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X2)) ) | (~spl7_4 | ~spl7_22 | ~spl7_25)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1111,f1135])).
% 1.71/0.64  fof(f1135,plain,(
% 1.71/0.64    r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~spl7_25),
% 1.71/0.64    inference(avatar_component_clause,[],[f1134])).
% 1.71/0.64  fof(f1111,plain,(
% 1.71/0.64    ( ! [X2] : (r1_orders_2(sK0,X2,sK6(sK0,sK2,sK3)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X2) | ~r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))) ) | (~spl7_4 | ~spl7_22)),
% 1.71/0.64    inference(superposition,[],[f119,f1085])).
% 1.71/0.64  fof(f1085,plain,(
% 1.71/0.64    sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | ~spl7_22),
% 1.71/0.64    inference(avatar_component_clause,[],[f1083])).
% 1.71/0.64  fof(f119,plain,(
% 1.71/0.64    ( ! [X0,X1] : (r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,X1) | ~r2_yellow_0(sK0,X0)) ) | ~spl7_4),
% 1.71/0.64    inference(subsumption_resolution,[],[f117,f86])).
% 1.71/0.64  fof(f117,plain,(
% 1.71/0.64    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~r2_yellow_0(sK0,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X0,X1) | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0))) ) | ~spl7_4),
% 1.71/0.64    inference(resolution,[],[f101,f67])).
% 1.71/0.64  fof(f67,plain,(
% 1.71/0.64    ( ! [X0,X3,X1] : (~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X3) | r1_orders_2(X0,X3,k2_yellow_0(X0,X1))) )),
% 1.71/0.64    inference(equality_resolution,[],[f54])).
% 1.71/0.64  fof(f54,plain,(
% 1.71/0.64    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X3) | r1_orders_2(X0,X3,X2) | k2_yellow_0(X0,X1) != X2) )),
% 1.71/0.64    inference(cnf_transformation,[],[f20])).
% 1.71/0.64  fof(f20,plain,(
% 1.71/0.64    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.71/0.64    inference(flattening,[],[f19])).
% 1.71/0.64  fof(f19,plain,(
% 1.71/0.64    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.71/0.64    inference(ennf_transformation,[],[f7])).
% 1.71/0.64  fof(f7,axiom,(
% 1.71/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 1.71/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_yellow_0)).
% 1.71/0.64  fof(f101,plain,(
% 1.71/0.64    ( ! [X25] : (m1_subset_1(k2_yellow_0(sK0,X25),u1_struct_0(sK0))) ) | ~spl7_4),
% 1.71/0.64    inference(resolution,[],[f86,f62])).
% 1.71/0.64  fof(f62,plain,(
% 1.71/0.64    ( ! [X0,X1] : (~l1_orders_2(X0) | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))) )),
% 1.71/0.64    inference(cnf_transformation,[],[f25])).
% 1.71/0.64  fof(f25,plain,(
% 1.71/0.64    ! [X0,X1] : (m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.71/0.64    inference(ennf_transformation,[],[f8])).
% 1.71/0.64  fof(f8,axiom,(
% 1.71/0.64    ! [X0,X1] : (l1_orders_2(X0) => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)))),
% 1.71/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_yellow_0)).
% 1.71/0.64  fof(f1160,plain,(
% 1.71/0.64    ~spl7_4 | ~spl7_5 | spl7_9 | spl7_27),
% 1.71/0.64    inference(avatar_contradiction_clause,[],[f1159])).
% 1.71/0.64  fof(f1159,plain,(
% 1.71/0.64    $false | (~spl7_4 | ~spl7_5 | spl7_9 | spl7_27)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1158,f127])).
% 1.71/0.64  fof(f1158,plain,(
% 1.71/0.64    r1_lattice3(sK0,sK2,sK3) | (~spl7_4 | ~spl7_5 | spl7_27)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1157,f105])).
% 1.71/0.64  fof(f1157,plain,(
% 1.71/0.64    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_lattice3(sK0,sK2,sK3) | (~spl7_4 | spl7_27)),
% 1.71/0.64    inference(resolution,[],[f1148,f99])).
% 1.71/0.64  fof(f99,plain,(
% 1.71/0.64    ( ! [X21,X22] : (r2_hidden(sK6(sK0,X22,X21),X22) | ~m1_subset_1(X21,u1_struct_0(sK0)) | r1_lattice3(sK0,X22,X21)) ) | ~spl7_4),
% 1.71/0.64    inference(resolution,[],[f86,f58])).
% 1.71/0.64  fof(f58,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(sK6(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f22])).
% 1.71/0.64  fof(f1148,plain,(
% 1.71/0.64    ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | spl7_27),
% 1.71/0.64    inference(avatar_component_clause,[],[f1146])).
% 1.71/0.64  fof(f1149,plain,(
% 1.71/0.64    ~spl7_27 | ~spl7_23 | spl7_25),
% 1.71/0.64    inference(avatar_split_clause,[],[f1144,f1134,f1087,f1146])).
% 1.71/0.64  fof(f1144,plain,(
% 1.71/0.64    ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | (~spl7_23 | spl7_25)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1142,f1088])).
% 1.71/0.64  fof(f1142,plain,(
% 1.71/0.64    ~r2_hidden(sK6(sK0,sK2,sK3),sK2) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | spl7_25),
% 1.71/0.64    inference(resolution,[],[f1136,f29])).
% 1.71/0.64  fof(f29,plain,(
% 1.71/0.64    ( ! [X4] : (r2_yellow_0(sK0,sK4(X4)) | ~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0))) )),
% 1.71/0.64    inference(cnf_transformation,[],[f16])).
% 1.71/0.64  fof(f1136,plain,(
% 1.71/0.64    ~r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | spl7_25),
% 1.71/0.64    inference(avatar_component_clause,[],[f1134])).
% 1.71/0.64  fof(f1095,plain,(
% 1.71/0.64    ~spl7_4 | ~spl7_5 | spl7_9 | spl7_23),
% 1.71/0.64    inference(avatar_contradiction_clause,[],[f1094])).
% 1.71/0.64  fof(f1094,plain,(
% 1.71/0.64    $false | (~spl7_4 | ~spl7_5 | spl7_9 | spl7_23)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1093,f127])).
% 1.71/0.64  fof(f1093,plain,(
% 1.71/0.64    r1_lattice3(sK0,sK2,sK3) | (~spl7_4 | ~spl7_5 | spl7_23)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1092,f86])).
% 1.71/0.64  fof(f1092,plain,(
% 1.71/0.64    ~l1_orders_2(sK0) | r1_lattice3(sK0,sK2,sK3) | (~spl7_5 | spl7_23)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1091,f105])).
% 1.71/0.64  fof(f1091,plain,(
% 1.71/0.64    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,sK2,sK3) | spl7_23),
% 1.71/0.64    inference(resolution,[],[f1089,f57])).
% 1.71/0.64  fof(f57,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f22])).
% 1.71/0.64  fof(f1089,plain,(
% 1.71/0.64    ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | spl7_23),
% 1.71/0.64    inference(avatar_component_clause,[],[f1087])).
% 1.71/0.64  fof(f1090,plain,(
% 1.71/0.64    spl7_22 | ~spl7_23 | ~spl7_4 | ~spl7_5 | spl7_9),
% 1.71/0.64    inference(avatar_split_clause,[],[f1032,f126,f103,f84,f1087,f1083])).
% 1.71/0.64  fof(f1032,plain,(
% 1.71/0.64    ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | (~spl7_4 | ~spl7_5 | spl7_9)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1025,f105])).
% 1.71/0.64  fof(f1025,plain,(
% 1.71/0.64    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) | sK6(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) | (~spl7_4 | spl7_9)),
% 1.71/0.64    inference(resolution,[],[f127,f132])).
% 1.71/0.64  fof(f132,plain,(
% 1.71/0.64    ( ! [X0] : (r1_lattice3(sK0,sK2,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0,sK2,X0),u1_struct_0(sK0)) | sK6(sK0,sK2,X0) = k2_yellow_0(sK0,sK4(sK6(sK0,sK2,X0)))) ) | ~spl7_4),
% 1.71/0.64    inference(resolution,[],[f99,f30])).
% 1.71/0.64  fof(f30,plain,(
% 1.71/0.64    ( ! [X4] : (~r2_hidden(X4,sK2) | ~m1_subset_1(X4,u1_struct_0(sK0)) | k2_yellow_0(sK0,sK4(X4)) = X4) )),
% 1.71/0.64    inference(cnf_transformation,[],[f16])).
% 1.71/0.64  fof(f1023,plain,(
% 1.71/0.64    ~spl7_8 | ~spl7_9),
% 1.71/0.64    inference(avatar_contradiction_clause,[],[f1022])).
% 1.71/0.64  fof(f1022,plain,(
% 1.71/0.64    $false | (~spl7_8 | ~spl7_9)),
% 1.71/0.64    inference(subsumption_resolution,[],[f1021,f124])).
% 1.71/0.64  fof(f1021,plain,(
% 1.71/0.64    ~r1_lattice3(sK0,sK1,sK3) | ~spl7_9),
% 1.71/0.64    inference(subsumption_resolution,[],[f32,f128])).
% 1.71/0.64  fof(f128,plain,(
% 1.71/0.64    r1_lattice3(sK0,sK2,sK3) | ~spl7_9),
% 1.71/0.64    inference(avatar_component_clause,[],[f126])).
% 1.71/0.64  fof(f32,plain,(
% 1.71/0.64    ~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 1.71/0.64    inference(cnf_transformation,[],[f16])).
% 1.71/0.64  fof(f1020,plain,(
% 1.71/0.64    ~spl7_12),
% 1.71/0.64    inference(avatar_contradiction_clause,[],[f1019])).
% 1.71/0.64  fof(f1019,plain,(
% 1.71/0.64    $false | ~spl7_12),
% 1.71/0.64    inference(subsumption_resolution,[],[f975,f42])).
% 1.71/0.64  fof(f42,plain,(
% 1.71/0.64    v1_xboole_0(k1_xboole_0)),
% 1.71/0.64    inference(cnf_transformation,[],[f1])).
% 1.71/0.64  fof(f1,axiom,(
% 1.71/0.64    v1_xboole_0(k1_xboole_0)),
% 1.71/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.71/0.64  fof(f975,plain,(
% 1.71/0.64    ~v1_xboole_0(k1_xboole_0) | ~spl7_12),
% 1.71/0.64    inference(superposition,[],[f43,f440])).
% 1.71/0.64  fof(f440,plain,(
% 1.71/0.64    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~spl7_12),
% 1.71/0.64    inference(avatar_component_clause,[],[f438])).
% 1.71/0.64  fof(f438,plain,(
% 1.71/0.64    spl7_12 <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 1.71/0.64  fof(f43,plain,(
% 1.71/0.64    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.71/0.64    inference(cnf_transformation,[],[f2])).
% 1.71/0.64  fof(f2,axiom,(
% 1.71/0.64    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.71/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.71/0.64  fof(f940,plain,(
% 1.71/0.64    spl7_12 | ~spl7_16 | spl7_20),
% 1.71/0.64    inference(avatar_contradiction_clause,[],[f939])).
% 1.71/0.64  fof(f939,plain,(
% 1.71/0.64    $false | (spl7_12 | ~spl7_16 | spl7_20)),
% 1.71/0.64    inference(subsumption_resolution,[],[f938,f44])).
% 1.71/0.64  fof(f44,plain,(
% 1.71/0.64    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 1.71/0.64    inference(cnf_transformation,[],[f5])).
% 1.71/0.64  fof(f5,axiom,(
% 1.71/0.64    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 1.71/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).
% 1.71/0.64  fof(f938,plain,(
% 1.71/0.64    ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | (spl7_12 | ~spl7_16 | spl7_20)),
% 1.71/0.64    inference(subsumption_resolution,[],[f937,f439])).
% 1.71/0.64  fof(f439,plain,(
% 1.71/0.64    k1_xboole_0 != k1_tarski(sK6(sK0,sK1,sK3)) | spl7_12),
% 1.71/0.64    inference(avatar_component_clause,[],[f438])).
% 1.71/0.64  fof(f937,plain,(
% 1.71/0.64    k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_16 | spl7_20)),
% 1.71/0.64    inference(subsumption_resolution,[],[f936,f606])).
% 1.71/0.64  fof(f606,plain,(
% 1.71/0.64    m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~spl7_16),
% 1.71/0.64    inference(avatar_component_clause,[],[f605])).
% 1.71/0.64  fof(f605,plain,(
% 1.71/0.64    spl7_16 <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 1.71/0.64  fof(f936,plain,(
% 1.71/0.64    ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_20),
% 1.71/0.64    inference(resolution,[],[f922,f35])).
% 1.71/0.64  fof(f35,plain,(
% 1.71/0.64    ( ! [X6] : (r2_yellow_0(sK0,X6) | ~m1_subset_1(X6,k1_zfmisc_1(sK1)) | k1_xboole_0 = X6 | ~v1_finset_1(X6)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f16])).
% 1.71/0.64  fof(f922,plain,(
% 1.71/0.64    ~r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | spl7_20),
% 1.71/0.64    inference(avatar_component_clause,[],[f920])).
% 1.71/0.64  fof(f920,plain,(
% 1.71/0.64    spl7_20 <=> r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 1.71/0.64  fof(f923,plain,(
% 1.71/0.64    ~spl7_20 | ~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_8 | ~spl7_9 | ~spl7_15),
% 1.71/0.64    inference(avatar_split_clause,[],[f904,f593,f126,f122,f103,f84,f79,f920])).
% 1.71/0.64  fof(f79,plain,(
% 1.71/0.64    spl7_3 <=> v4_orders_2(sK0)),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 1.71/0.64  fof(f593,plain,(
% 1.71/0.64    spl7_15 <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 1.71/0.64  fof(f904,plain,(
% 1.71/0.64    ~r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_3 | ~spl7_4 | ~spl7_5 | spl7_8 | ~spl7_9 | ~spl7_15)),
% 1.71/0.64    inference(subsumption_resolution,[],[f899,f123])).
% 1.71/0.64  fof(f123,plain,(
% 1.71/0.64    ~r1_lattice3(sK0,sK1,sK3) | spl7_8),
% 1.71/0.64    inference(avatar_component_clause,[],[f122])).
% 1.71/0.64  fof(f899,plain,(
% 1.71/0.64    r1_lattice3(sK0,sK1,sK3) | ~r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_15)),
% 1.71/0.64    inference(resolution,[],[f735,f120])).
% 1.71/0.64  fof(f120,plain,(
% 1.71/0.64    ( ! [X2] : (r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) | ~r2_yellow_0(sK0,X2)) ) | ~spl7_4),
% 1.71/0.64    inference(subsumption_resolution,[],[f118,f86])).
% 1.71/0.64  fof(f118,plain,(
% 1.71/0.64    ( ! [X2] : (~l1_orders_2(sK0) | ~r2_yellow_0(sK0,X2) | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2))) ) | ~spl7_4),
% 1.71/0.64    inference(resolution,[],[f101,f66])).
% 1.71/0.64  fof(f66,plain,(
% 1.71/0.64    ( ! [X0,X1] : (~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_yellow_0(X0,X1) | r1_lattice3(X0,X1,k2_yellow_0(X0,X1))) )),
% 1.71/0.64    inference(equality_resolution,[],[f55])).
% 1.71/0.64  fof(f55,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | r1_lattice3(X0,X1,X2) | k2_yellow_0(X0,X1) != X2) )),
% 1.71/0.64    inference(cnf_transformation,[],[f20])).
% 1.71/0.64  fof(f735,plain,(
% 1.71/0.64    ( ! [X4] : (~r1_lattice3(sK0,k1_tarski(sK6(sK0,X4,sK3)),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | r1_lattice3(sK0,X4,sK3)) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_9 | ~spl7_15)),
% 1.71/0.64    inference(subsumption_resolution,[],[f734,f128])).
% 1.71/0.64  fof(f734,plain,(
% 1.71/0.64    ( ! [X4] : (r1_lattice3(sK0,X4,sK3) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X4,sK3)),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | ~r1_lattice3(sK0,sK2,sK3)) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15)),
% 1.71/0.64    inference(subsumption_resolution,[],[f709,f101])).
% 1.71/0.64  fof(f709,plain,(
% 1.71/0.64    ( ! [X4] : (r1_lattice3(sK0,X4,sK3) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X4,sK3)),k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) | ~m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK2,sK3)) ) | (~spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_15)),
% 1.71/0.64    inference(resolution,[],[f594,f361])).
% 1.71/0.64  fof(f361,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | r1_lattice3(sK0,X1,sK3) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X1,sK3)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X2,sK3)) ) | (~spl7_3 | ~spl7_4 | ~spl7_5)),
% 1.71/0.64    inference(subsumption_resolution,[],[f360,f105])).
% 1.71/0.64  fof(f360,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,X1,sK3) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X1,sK3)),X0) | ~r2_hidden(X0,X2) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X2,sK3)) ) | (~spl7_3 | ~spl7_4 | ~spl7_5)),
% 1.71/0.64    inference(duplicate_literal_removal,[],[f354])).
% 1.71/0.64  fof(f354,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattice3(sK0,X1,sK3) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X1,sK3)),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X2) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X2,sK3)) ) | (~spl7_3 | ~spl7_4 | ~spl7_5)),
% 1.71/0.64    inference(resolution,[],[f301,f98])).
% 1.71/0.64  fof(f98,plain,(
% 1.71/0.64    ( ! [X19,X20,X18] : (r1_orders_2(sK0,X18,X19) | ~m1_subset_1(X19,u1_struct_0(sK0)) | ~r2_hidden(X19,X20) | ~m1_subset_1(X18,u1_struct_0(sK0)) | ~r1_lattice3(sK0,X20,X18)) ) | ~spl7_4),
% 1.71/0.64    inference(resolution,[],[f86,f56])).
% 1.71/0.64  fof(f56,plain,(
% 1.71/0.64    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X3,X1) | r1_orders_2(X0,X2,X3) | ~r1_lattice3(X0,X1,X2)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f22])).
% 1.71/0.64  fof(f301,plain,(
% 1.71/0.64    ( ! [X0,X1] : (~r1_orders_2(sK0,sK3,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,sK3) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,sK3)),X1)) ) | (~spl7_3 | ~spl7_4 | ~spl7_5)),
% 1.71/0.64    inference(resolution,[],[f212,f105])).
% 1.71/0.64  fof(f212,plain,(
% 1.71/0.64    ( ! [X4,X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattice3(sK0,X3,X2) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X4) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X3,X2)),X4)) ) | (~spl7_3 | ~spl7_4)),
% 1.71/0.64    inference(duplicate_literal_removal,[],[f209])).
% 1.71/0.64  fof(f209,plain,(
% 1.71/0.64    ( ! [X4,X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_lattice3(sK0,X3,X2) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X2,X4) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X3,X2)),X4) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | (~spl7_3 | ~spl7_4)),
% 1.71/0.64    inference(resolution,[],[f195,f157])).
% 1.71/0.64  fof(f157,plain,(
% 1.71/0.64    ( ! [X4,X5,X3] : (r1_lattice3(sK0,X5,X3) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X4) | ~r1_lattice3(sK0,X5,X4) | ~m1_subset_1(X3,u1_struct_0(sK0))) ) | (~spl7_3 | ~spl7_4)),
% 1.71/0.64    inference(subsumption_resolution,[],[f89,f86])).
% 1.71/0.64  fof(f89,plain,(
% 1.71/0.64    ( ! [X4,X5,X3] : (~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X3,X4) | ~r1_lattice3(sK0,X5,X4) | r1_lattice3(sK0,X5,X3)) ) | ~spl7_3),
% 1.71/0.64    inference(resolution,[],[f81,f61])).
% 1.71/0.64  fof(f61,plain,(
% 1.71/0.64    ( ! [X2,X0,X3,X1] : (~v4_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,X3,X2) | r1_lattice3(X0,X3,X1)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f24])).
% 1.71/0.64  fof(f24,plain,(
% 1.71/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 1.71/0.64    inference(flattening,[],[f23])).
% 1.71/0.64  fof(f23,plain,(
% 1.71/0.64    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((r2_lattice3(X0,X3,X2) | ~r2_lattice3(X0,X3,X1)) & (r1_lattice3(X0,X3,X1) | ~r1_lattice3(X0,X3,X2))) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 1.71/0.64    inference(ennf_transformation,[],[f9])).
% 1.71/0.64  fof(f9,axiom,(
% 1.71/0.64    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) => ! [X3] : ((r2_lattice3(X0,X3,X1) => r2_lattice3(X0,X3,X2)) & (r1_lattice3(X0,X3,X2) => r1_lattice3(X0,X3,X1)))))))),
% 1.71/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_0)).
% 1.71/0.64  fof(f81,plain,(
% 1.71/0.64    v4_orders_2(sK0) | ~spl7_3),
% 1.71/0.64    inference(avatar_component_clause,[],[f79])).
% 1.71/0.64  fof(f195,plain,(
% 1.71/0.64    ( ! [X0,X1] : (~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)) ) | ~spl7_4),
% 1.71/0.64    inference(subsumption_resolution,[],[f194,f86])).
% 1.71/0.64  fof(f194,plain,(
% 1.71/0.64    ( ! [X0,X1] : (~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1) | ~l1_orders_2(sK0)) ) | ~spl7_4),
% 1.71/0.64    inference(duplicate_literal_removal,[],[f193])).
% 1.71/0.64  fof(f193,plain,(
% 1.71/0.64    ( ! [X0,X1] : (~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,X0,X1)) ) | ~spl7_4),
% 1.71/0.64    inference(resolution,[],[f146,f57])).
% 1.71/0.64  fof(f146,plain,(
% 1.71/0.64    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)) ) | ~spl7_4),
% 1.71/0.64    inference(duplicate_literal_removal,[],[f145])).
% 1.71/0.64  fof(f145,plain,(
% 1.71/0.64    ( ! [X0,X1] : (~m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattice3(sK0,X0,X1)) ) | ~spl7_4),
% 1.71/0.64    inference(resolution,[],[f93,f100])).
% 1.71/0.64  fof(f93,plain,(
% 1.71/0.64    ( ! [X6,X7] : (r1_orders_2(sK0,X6,X7) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(X7),X6) | ~m1_subset_1(X6,u1_struct_0(sK0))) ) | ~spl7_4),
% 1.71/0.64    inference(resolution,[],[f86,f48])).
% 1.71/0.64  fof(f48,plain,(
% 1.71/0.64    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_lattice3(X0,k1_tarski(X2),X1) | r1_orders_2(X0,X1,X2)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f17])).
% 1.71/0.64  fof(f17,plain,(
% 1.71/0.64    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 1.71/0.64    inference(ennf_transformation,[],[f10])).
% 1.71/0.64  fof(f10,axiom,(
% 1.71/0.64    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 1.71/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_yellow_0)).
% 1.71/0.64  fof(f594,plain,(
% 1.71/0.64    r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | ~spl7_15),
% 1.71/0.64    inference(avatar_component_clause,[],[f593])).
% 1.71/0.64  fof(f645,plain,(
% 1.71/0.64    ~spl7_4 | ~spl7_5 | spl7_8 | spl7_17),
% 1.71/0.64    inference(avatar_contradiction_clause,[],[f644])).
% 1.71/0.64  fof(f644,plain,(
% 1.71/0.64    $false | (~spl7_4 | ~spl7_5 | spl7_8 | spl7_17)),
% 1.71/0.64    inference(subsumption_resolution,[],[f643,f123])).
% 1.71/0.64  fof(f643,plain,(
% 1.71/0.64    r1_lattice3(sK0,sK1,sK3) | (~spl7_4 | ~spl7_5 | spl7_17)),
% 1.71/0.64    inference(subsumption_resolution,[],[f642,f105])).
% 1.71/0.64  fof(f642,plain,(
% 1.71/0.64    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r1_lattice3(sK0,sK1,sK3) | (~spl7_4 | spl7_17)),
% 1.71/0.64    inference(resolution,[],[f628,f99])).
% 1.71/0.64  fof(f628,plain,(
% 1.71/0.64    ~r2_hidden(sK6(sK0,sK1,sK3),sK1) | spl7_17),
% 1.71/0.64    inference(avatar_component_clause,[],[f626])).
% 1.71/0.64  fof(f626,plain,(
% 1.71/0.64    spl7_17 <=> r2_hidden(sK6(sK0,sK1,sK3),sK1)),
% 1.71/0.64    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 1.71/0.64  fof(f629,plain,(
% 1.71/0.64    ~spl7_17 | spl7_16),
% 1.71/0.64    inference(avatar_split_clause,[],[f620,f605,f626])).
% 1.71/0.64  fof(f620,plain,(
% 1.71/0.64    ~r2_hidden(sK6(sK0,sK1,sK3),sK1) | spl7_16),
% 1.71/0.64    inference(resolution,[],[f607,f63])).
% 1.71/0.64  fof(f63,plain,(
% 1.71/0.64    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f26])).
% 1.71/0.64  fof(f26,plain,(
% 1.71/0.64    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.71/0.64    inference(ennf_transformation,[],[f3])).
% 1.71/0.64  fof(f3,axiom,(
% 1.71/0.64    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.71/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 1.71/0.64  fof(f607,plain,(
% 1.71/0.64    ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | spl7_16),
% 1.71/0.64    inference(avatar_component_clause,[],[f605])).
% 1.71/0.64  fof(f608,plain,(
% 1.71/0.64    ~spl7_16 | spl7_12 | spl7_15),
% 1.71/0.64    inference(avatar_split_clause,[],[f599,f593,f438,f605])).
% 1.71/0.64  fof(f599,plain,(
% 1.71/0.64    ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | (spl7_12 | spl7_15)),
% 1.71/0.64    inference(subsumption_resolution,[],[f598,f44])).
% 1.71/0.64  fof(f598,plain,(
% 1.71/0.64    ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | (spl7_12 | spl7_15)),
% 1.71/0.64    inference(subsumption_resolution,[],[f597,f439])).
% 1.71/0.64  fof(f597,plain,(
% 1.71/0.64    ~m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) | ~v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3))) | spl7_15),
% 1.71/0.64    inference(resolution,[],[f595,f34])).
% 1.71/0.64  fof(f34,plain,(
% 1.71/0.64    ( ! [X3] : (r2_hidden(k2_yellow_0(sK0,X3),sK2) | ~m1_subset_1(X3,k1_zfmisc_1(sK1)) | k1_xboole_0 = X3 | ~v1_finset_1(X3)) )),
% 1.71/0.64    inference(cnf_transformation,[],[f16])).
% 1.71/0.64  fof(f595,plain,(
% 1.71/0.64    ~r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) | spl7_15),
% 1.71/0.64    inference(avatar_component_clause,[],[f593])).
% 1.71/0.64  fof(f129,plain,(
% 1.71/0.64    spl7_8 | spl7_9),
% 1.71/0.64    inference(avatar_split_clause,[],[f31,f126,f122])).
% 1.71/0.64  fof(f31,plain,(
% 1.71/0.64    r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)),
% 1.71/0.64    inference(cnf_transformation,[],[f16])).
% 1.71/0.64  fof(f106,plain,(
% 1.71/0.64    spl7_5),
% 1.71/0.64    inference(avatar_split_clause,[],[f33,f103])).
% 1.71/0.64  fof(f33,plain,(
% 1.71/0.64    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.71/0.64    inference(cnf_transformation,[],[f16])).
% 1.71/0.64  fof(f87,plain,(
% 1.71/0.64    spl7_4),
% 1.71/0.64    inference(avatar_split_clause,[],[f41,f84])).
% 1.71/0.64  fof(f41,plain,(
% 1.71/0.64    l1_orders_2(sK0)),
% 1.71/0.64    inference(cnf_transformation,[],[f16])).
% 1.71/0.64  fof(f82,plain,(
% 1.71/0.64    spl7_3),
% 1.71/0.64    inference(avatar_split_clause,[],[f40,f79])).
% 1.71/0.64  fof(f40,plain,(
% 1.71/0.64    v4_orders_2(sK0)),
% 1.71/0.64    inference(cnf_transformation,[],[f16])).
% 1.71/0.64  % SZS output end Proof for theBenchmark
% 1.71/0.64  % (9995)------------------------------
% 1.71/0.64  % (9995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.64  % (9995)Termination reason: Refutation
% 1.71/0.65  
% 1.71/0.65  % (9995)Memory used [KB]: 11257
% 1.71/0.65  % (9995)Time elapsed: 0.198 s
% 1.71/0.65  % (9995)------------------------------
% 1.71/0.65  % (9995)------------------------------
% 1.71/0.65  % (9991)Success in time 0.288 s
%------------------------------------------------------------------------------
