%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1672+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:18 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :  214 ( 457 expanded)
%              Number of leaves         :   38 ( 166 expanded)
%              Depth                    :   21
%              Number of atoms          :  893 (2666 expanded)
%              Number of equality atoms :   34 ( 206 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1789,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f109,f114,f119,f137,f155,f158,f168,f196,f224,f235,f260,f279,f357,f366,f408,f550,f672,f712,f774,f783,f955,f976,f1746,f1765,f1788])).

fof(f1788,plain,
    ( ~ spl7_23
    | spl7_60
    | spl7_110 ),
    inference(avatar_contradiction_clause,[],[f1787])).

fof(f1787,plain,
    ( $false
    | ~ spl7_23
    | spl7_60
    | spl7_110 ),
    inference(subsumption_resolution,[],[f1786,f46])).

fof(f46,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f1786,plain,
    ( ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_23
    | spl7_60
    | spl7_110 ),
    inference(subsumption_resolution,[],[f1785,f953])).

fof(f953,plain,
    ( k1_xboole_0 != k1_tarski(sK6(sK0,sK1,sK3))
    | spl7_60 ),
    inference(avatar_component_clause,[],[f952])).

fof(f952,plain,
    ( spl7_60
  <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f1785,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_23
    | spl7_110 ),
    inference(subsumption_resolution,[],[f1784,f278])).

fof(f278,plain,
    ( m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl7_23
  <=> m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f1784,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_110 ),
    inference(resolution,[],[f1764,f38])).

fof(f38,plain,(
    ! [X6] :
      ( r1_yellow_0(sK0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
      | k1_xboole_0 = X6
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <~> r2_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X7] :
                  ( ( r2_lattice3(X0,X1,X7)
                  <~> r2_lattice3(X0,X2,X7) )
                  & m1_subset_1(X7,u1_struct_0(X0)) )
              & ! [X3] :
                  ( r2_hidden(k1_yellow_0(X0,X3),X2)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X3) )
              & ! [X4] :
                  ( ? [X5] :
                      ( k1_yellow_0(X0,X5) = X4
                      & r1_yellow_0(X0,X5)
                      & m1_subset_1(X5,k1_zfmisc_1(X1))
                      & v1_finset_1(X5) )
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & ! [X6] :
                  ( r1_yellow_0(X0,X6)
                  | k1_xboole_0 = X6
                  | ~ m1_subset_1(X6,k1_zfmisc_1(X1))
                  | ~ v1_finset_1(X6) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
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
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( ! [X5] :
                                ( ( m1_subset_1(X5,k1_zfmisc_1(X1))
                                  & v1_finset_1(X5) )
                               => ~ ( k1_yellow_0(X0,X5) = X4
                                    & r1_yellow_0(X0,X5) ) )
                            & r2_hidden(X4,X2) ) )
                    & ! [X6] :
                        ( ( m1_subset_1(X6,k1_zfmisc_1(X1))
                          & v1_finset_1(X6) )
                       => ( k1_xboole_0 != X6
                         => r1_yellow_0(X0,X6) ) ) )
                 => ! [X7] :
                      ( m1_subset_1(X7,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X7)
                      <=> r2_lattice3(X0,X2,X7) ) ) ) ) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,negated_conjecture,(
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
                         => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                    & ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ~ ( ! [X4] :
                                ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                  & v1_finset_1(X4) )
                               => ~ ( k1_yellow_0(X0,X4) = X3
                                    & r1_yellow_0(X0,X4) ) )
                            & r2_hidden(X3,X2) ) )
                    & ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                          & v1_finset_1(X3) )
                       => ( k1_xboole_0 != X3
                         => r1_yellow_0(X0,X3) ) ) )
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_lattice3(X0,X1,X3)
                      <=> r2_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
                       => r2_hidden(k1_yellow_0(X0,X3),X2) ) )
                  & ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ~ ( ! [X4] :
                              ( ( m1_subset_1(X4,k1_zfmisc_1(X1))
                                & v1_finset_1(X4) )
                             => ~ ( k1_yellow_0(X0,X4) = X3
                                  & r1_yellow_0(X0,X4) ) )
                          & r2_hidden(X3,X2) ) )
                  & ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(X1))
                        & v1_finset_1(X3) )
                     => ( k1_xboole_0 != X3
                       => r1_yellow_0(X0,X3) ) ) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                    <=> r2_lattice3(X0,X2,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_waybel_0)).

fof(f1764,plain,
    ( ~ r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_110 ),
    inference(avatar_component_clause,[],[f1762])).

fof(f1762,plain,
    ( spl7_110
  <=> r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_110])])).

fof(f1765,plain,
    ( ~ spl7_110
    | ~ spl7_4
    | spl7_109 ),
    inference(avatar_split_clause,[],[f1748,f1743,f88,f1762])).

fof(f88,plain,
    ( spl7_4
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f1743,plain,
    ( spl7_109
  <=> r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_109])])).

fof(f1748,plain,
    ( ~ r1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_4
    | spl7_109 ),
    inference(resolution,[],[f1745,f148])).

fof(f148,plain,
    ( ! [X2] :
        ( r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2))
        | ~ r1_yellow_0(sK0,X2) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f146,f90])).

fof(f90,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f146,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X2)
        | r2_lattice3(sK0,X2,k1_yellow_0(sK0,X2)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f104,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,k1_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | r2_lattice3(X0,X1,X2)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f104,plain,
    ( ! [X25] : m1_subset_1(k1_yellow_0(sK0,X25),u1_struct_0(sK0))
    | ~ spl7_4 ),
    inference(resolution,[],[f90,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow_0)).

fof(f1745,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | spl7_109 ),
    inference(avatar_component_clause,[],[f1743])).

fof(f1746,plain,
    ( ~ spl7_109
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_59 ),
    inference(avatar_split_clause,[],[f1141,f948,f232,f134,f130,f106,f88,f83,f1743])).

fof(f83,plain,
    ( spl7_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f106,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f130,plain,
    ( spl7_9
  <=> r2_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f134,plain,
    ( spl7_10
  <=> r2_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f232,plain,
    ( spl7_20
  <=> m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f948,plain,
    ( spl7_59
  <=> r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_59])])).

fof(f1141,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_10
    | ~ spl7_20
    | ~ spl7_59 ),
    inference(subsumption_resolution,[],[f1140,f136])).

fof(f136,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f1140,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | ~ r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_20
    | ~ spl7_59 ),
    inference(subsumption_resolution,[],[f1139,f104])).

fof(f1139,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))))
    | ~ m1_subset_1(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_20
    | ~ spl7_59 ),
    inference(resolution,[],[f807,f950])).

fof(f950,plain,
    ( r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_59 ),
    inference(avatar_component_clause,[],[f948])).

fof(f807,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,X3)
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X3,sK3) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f803,f108])).

fof(f108,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f106])).

fof(f803,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X2)
        | ~ r2_hidden(X2,X3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X3,sK3) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_20 ),
    inference(duplicate_literal_removal,[],[f796])).

fof(f796,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X3,sK3) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_20 ),
    inference(resolution,[],[f765,f101])).

fof(f101,plain,
    ( ! [X19,X20,X18] :
        ( r1_orders_2(sK0,X19,X18)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | ~ r2_hidden(X19,X20)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X20,X18) )
    | ~ spl7_4 ),
    inference(resolution,[],[f90,f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X3,X2)
      | ~ r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f765,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK0,X5,sK3)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X5) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f758,f234])).

fof(f234,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f232])).

fof(f758,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK0,X5,sK3)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X5) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_20 ),
    inference(duplicate_literal_removal,[],[f757])).

fof(f757,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK0,X5,sK3)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_20 ),
    inference(resolution,[],[f753,f94])).

fof(f94,plain,
    ( ! [X2,X3] :
        ( r1_orders_2(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(X3),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f90,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k1_tarski(X2),X1)
      | r1_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f753,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),X0)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f721,f234])).

fof(f721,plain,
    ( ! [X0] :
        ( ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),X0)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(subsumption_resolution,[],[f716,f108])).

fof(f716,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK0,sK1,sK3),X0)
        | ~ r1_orders_2(sK0,X0,sK3)
        | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9 ),
    inference(resolution,[],[f131,f213])).

fof(f213,plain,
    ( ! [X2,X0,X1] :
        ( r2_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK0,X2,X1),X0)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK6(sK0,X2,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK6(sK0,X2,X1),X0)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK6(sK0,X2,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X2,X1) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f199,f103])).

fof(f103,plain,
    ( ! [X24,X23] :
        ( ~ r1_orders_2(sK0,sK6(sK0,X24,X23),X23)
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | r2_lattice3(sK0,X24,X23) )
    | ~ spl7_4 ),
    inference(resolution,[],[f90,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f199,plain,
    ( ! [X2,X0,X1] :
        ( r1_orders_2(sK0,X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f92,f90])).

fof(f92,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r1_orders_2(sK0,X1,X2)
        | r1_orders_2(sK0,X0,X2) )
    | ~ spl7_3 ),
    inference(resolution,[],[f85,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_orders_2)).

fof(f85,plain,
    ( v4_orders_2(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f131,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f976,plain,
    ( spl7_50
    | ~ spl7_60 ),
    inference(avatar_contradiction_clause,[],[f975])).

fof(f975,plain,
    ( $false
    | spl7_50
    | ~ spl7_60 ),
    inference(subsumption_resolution,[],[f962,f45])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f962,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl7_50
    | ~ spl7_60 ),
    inference(superposition,[],[f782,f954])).

fof(f954,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f952])).

fof(f782,plain,
    ( ~ v1_xboole_0(k1_tarski(sK6(sK0,sK1,sK3)))
    | spl7_50 ),
    inference(avatar_component_clause,[],[f780])).

fof(f780,plain,
    ( spl7_50
  <=> v1_xboole_0(k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f955,plain,
    ( spl7_59
    | spl7_60
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f752,f276,f952,f948])).

fof(f752,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_23 ),
    inference(subsumption_resolution,[],[f748,f46])).

fof(f748,plain,
    ( ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | r2_hidden(k1_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl7_23 ),
    inference(resolution,[],[f278,f37])).

fof(f37,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X3)
      | k1_xboole_0 = X3
      | r2_hidden(k1_yellow_0(sK0,X3),sK2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f783,plain,
    ( ~ spl7_50
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f777,f771,f780])).

fof(f771,plain,
    ( spl7_49
  <=> r2_hidden(sK6(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3),k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f777,plain,
    ( ~ v1_xboole_0(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_49 ),
    inference(resolution,[],[f773,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f773,plain,
    ( r2_hidden(sK6(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3),k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f771])).

fof(f774,plain,
    ( spl7_49
    | ~ spl7_4
    | ~ spl7_5
    | spl7_22 ),
    inference(avatar_split_clause,[],[f742,f257,f106,f88,f771])).

fof(f257,plain,
    ( spl7_22
  <=> r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f742,plain,
    ( r2_hidden(sK6(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3),k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl7_4
    | ~ spl7_5
    | spl7_22 ),
    inference(subsumption_resolution,[],[f737,f108])).

fof(f737,plain,
    ( r2_hidden(sK6(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3),k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4
    | spl7_22 ),
    inference(resolution,[],[f259,f102])).

fof(f102,plain,
    ( ! [X21,X22] :
        ( r2_lattice3(sK0,X22,X21)
        | r2_hidden(sK6(sK0,X22,X21),X22)
        | ~ m1_subset_1(X21,u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(resolution,[],[f90,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f259,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f257])).

fof(f712,plain,
    ( ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_27
    | spl7_48 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_9
    | ~ spl7_27
    | spl7_48 ),
    inference(subsumption_resolution,[],[f710,f132])).

fof(f132,plain,
    ( r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f710,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_27
    | spl7_48 ),
    inference(resolution,[],[f695,f365])).

fof(f365,plain,
    ( r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1)
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl7_27
  <=> r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f695,plain,
    ( ! [X1] :
        ( ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X1)
        | ~ r2_lattice3(sK0,X1,sK3) )
    | ~ spl7_4
    | ~ spl7_5
    | spl7_48 ),
    inference(subsumption_resolution,[],[f690,f108])).

fof(f690,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X1,sK3)
        | ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X1) )
    | ~ spl7_4
    | spl7_48 ),
    inference(resolution,[],[f671,f97])).

fof(f97,plain,
    ( ! [X10,X8,X9] :
        ( r2_lattice3(sK0,X8,X10)
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X9,X10)
        | ~ r1_tarski(X8,X9) )
    | ~ spl7_4 ),
    inference(resolution,[],[f90,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X2,X3)
      | r2_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f671,plain,
    ( ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | spl7_48 ),
    inference(avatar_component_clause,[],[f669])).

fof(f669,plain,
    ( spl7_48
  <=> r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f672,plain,
    ( ~ spl7_48
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10
    | ~ spl7_31
    | ~ spl7_41 ),
    inference(avatar_split_clause,[],[f664,f538,f405,f134,f106,f88,f669])).

fof(f405,plain,
    ( spl7_31
  <=> sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f538,plain,
    ( spl7_41
  <=> r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_41])])).

fof(f664,plain,
    ( ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10
    | ~ spl7_31
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f663,f135])).

fof(f135,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f134])).

fof(f663,plain,
    ( ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_31
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f662,f108])).

fof(f662,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_31
    | ~ spl7_41 ),
    inference(duplicate_literal_removal,[],[f656])).

fof(f656,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_31
    | ~ spl7_41 ),
    inference(resolution,[],[f655,f103])).

fof(f655,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0) )
    | ~ spl7_4
    | ~ spl7_31
    | ~ spl7_41 ),
    inference(subsumption_resolution,[],[f409,f539])).

fof(f539,plain,
    ( r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_41 ),
    inference(avatar_component_clause,[],[f538])).

fof(f409,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,sK6(sK0,sK2,sK3),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) )
    | ~ spl7_4
    | ~ spl7_31 ),
    inference(superposition,[],[f147,f407])).

fof(f407,plain,
    ( sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f405])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | ~ r1_yellow_0(sK0,X0) )
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f145,f90])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ r1_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,k1_yellow_0(sK0,X0),X1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f104,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k1_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,k1_yellow_0(X0,X1),X3) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X2,X3)
      | k1_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f550,plain,
    ( ~ spl7_13
    | ~ spl7_16
    | spl7_41 ),
    inference(avatar_contradiction_clause,[],[f549])).

fof(f549,plain,
    ( $false
    | ~ spl7_13
    | ~ spl7_16
    | spl7_41 ),
    inference(subsumption_resolution,[],[f548,f195])).

fof(f195,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f193])).

fof(f193,plain,
    ( spl7_16
  <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f548,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_13
    | spl7_41 ),
    inference(subsumption_resolution,[],[f546,f167])).

fof(f167,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl7_13
  <=> r2_hidden(sK6(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f546,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_41 ),
    inference(resolution,[],[f540,f32])).

fof(f32,plain,(
    ! [X4] :
      ( r1_yellow_0(sK0,sK4(X4))
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f540,plain,
    ( ~ r1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | spl7_41 ),
    inference(avatar_component_clause,[],[f538])).

fof(f408,plain,
    ( spl7_31
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f334,f193,f165,f405])).

fof(f334,plain,
    ( sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f329,f195])).

fof(f329,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | sK6(sK0,sK2,sK3) = k1_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl7_13 ),
    inference(resolution,[],[f167,f33])).

fof(f33,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k1_yellow_0(sK0,sK4(X4)) = X4 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f366,plain,
    ( spl7_27
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f361,f354,f363])).

fof(f354,plain,
    ( spl7_26
  <=> m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f361,plain,
    ( r1_tarski(sK4(sK6(sK0,sK2,sK3)),sK1)
    | ~ spl7_26 ),
    inference(resolution,[],[f356,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f356,plain,
    ( m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f354])).

fof(f357,plain,
    ( spl7_26
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f335,f193,f165,f354])).

fof(f335,plain,
    ( m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f330,f195])).

fof(f330,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_13 ),
    inference(resolution,[],[f167,f31])).

fof(f31,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | m1_subset_1(sK4(X4),k1_zfmisc_1(sK1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f279,plain,
    ( spl7_23
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f228,f221,f276])).

fof(f221,plain,
    ( spl7_19
  <=> r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f228,plain,
    ( m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_19 ),
    inference(resolution,[],[f223,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f223,plain,
    ( r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f221])).

fof(f260,plain,
    ( ~ spl7_22
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f255,f232,f130,f106,f88,f257])).

fof(f255,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f226,f234])).

fof(f226,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(subsumption_resolution,[],[f225,f108])).

fof(f225,plain,
    ( ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl7_4
    | spl7_9 ),
    inference(resolution,[],[f180,f131])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( r2_lattice3(sK0,X0,X1)
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0)) )
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r2_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_lattice3(sK0,X0,X1) )
    | ~ spl7_4 ),
    inference(resolution,[],[f94,f103])).

fof(f235,plain,
    ( spl7_20
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f209,f152,f116,f232])).

fof(f116,plain,
    ( spl7_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f152,plain,
    ( spl7_12
  <=> r2_hidden(sK6(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f209,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(resolution,[],[f154,f122])).

fof(f122,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_7 ),
    inference(resolution,[],[f118,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f118,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f116])).

fof(f154,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f152])).

fof(f224,plain,
    ( spl7_19
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f211,f152,f221])).

fof(f211,plain,
    ( r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f154,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f196,plain,
    ( spl7_16
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f169,f165,f111,f193])).

fof(f111,plain,
    ( spl7_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f169,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(resolution,[],[f167,f120])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_6 ),
    inference(resolution,[],[f113,f69])).

fof(f113,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f111])).

fof(f168,plain,
    ( spl7_13
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10 ),
    inference(avatar_split_clause,[],[f161,f134,f106,f88,f165])).

fof(f161,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10 ),
    inference(subsumption_resolution,[],[f160,f108])).

fof(f160,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4
    | spl7_10 ),
    inference(resolution,[],[f135,f102])).

fof(f158,plain,
    ( ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f156,f132])).

fof(f156,plain,
    ( ~ r2_lattice3(sK0,sK1,sK3)
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f35,f136])).

fof(f35,plain,
    ( ~ r2_lattice3(sK0,sK2,sK3)
    | ~ r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f155,plain,
    ( spl7_12
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(avatar_split_clause,[],[f150,f130,f106,f88,f152])).

fof(f150,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(subsumption_resolution,[],[f149,f108])).

fof(f149,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4
    | spl7_9 ),
    inference(resolution,[],[f102,f131])).

fof(f137,plain,
    ( spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f34,f134,f130])).

fof(f34,plain,
    ( r2_lattice3(sK0,sK2,sK3)
    | r2_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f119,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f40,f116])).

fof(f40,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f114,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f39,f111])).

fof(f39,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f109,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f36,f106])).

fof(f36,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f91,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f44,f88])).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f43,f83])).

fof(f43,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
