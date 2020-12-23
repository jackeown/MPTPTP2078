%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : waybel_0__t57_waybel_0.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:00 EDT 2019

% Result     : Theorem 2.43s
% Output     : Refutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :  216 ( 453 expanded)
%              Number of leaves         :   41 ( 156 expanded)
%              Depth                    :   22
%              Number of atoms          :  917 (2705 expanded)
%              Number of equality atoms :   36 ( 207 expanded)
%              Maximal formula depth    :   19 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3979,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f166,f173,f203,f210,f217,f234,f248,f251,f329,f460,f470,f510,f578,f656,f764,f765,f834,f998,f1548,f1620,f3888,f3921,f3945,f3956,f3978])).

fof(f3978,plain,
    ( ~ spl12_16
    | ~ spl12_78
    | ~ spl12_378 ),
    inference(avatar_contradiction_clause,[],[f3977])).

fof(f3977,plain,
    ( $false
    | ~ spl12_16
    | ~ spl12_78
    | ~ spl12_378 ),
    inference(subsumption_resolution,[],[f3975,f233])).

fof(f233,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl12_16 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl12_16
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_16])])).

fof(f3975,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ spl12_78
    | ~ spl12_378 ),
    inference(resolution,[],[f3887,f757])).

fof(f757,plain,
    ( r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl12_78 ),
    inference(avatar_component_clause,[],[f756])).

fof(f756,plain,
    ( spl12_78
  <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_78])])).

fof(f3887,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),X2)
        | ~ r1_lattice3(sK0,X2,sK3) )
    | ~ spl12_378 ),
    inference(avatar_component_clause,[],[f3886])).

fof(f3886,plain,
    ( spl12_378
  <=> ! [X2] :
        ( ~ r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),X2)
        | ~ r1_lattice3(sK0,X2,sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_378])])).

fof(f3956,plain,
    ( ~ spl12_18
    | spl12_383 ),
    inference(avatar_contradiction_clause,[],[f3955])).

fof(f3955,plain,
    ( $false
    | ~ spl12_18
    | ~ spl12_383 ),
    inference(subsumption_resolution,[],[f3953,f247])).

fof(f247,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f246])).

fof(f246,plain,
    ( spl12_18
  <=> r2_hidden(sK6(sK0,sK1,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f3953,plain,
    ( ~ r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ spl12_383 ),
    inference(resolution,[],[f3944,f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',t37_zfmisc_1)).

fof(f3944,plain,
    ( ~ r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)
    | ~ spl12_383 ),
    inference(avatar_component_clause,[],[f3943])).

fof(f3943,plain,
    ( spl12_383
  <=> ~ r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_383])])).

fof(f3945,plain,
    ( ~ spl12_383
    | spl12_381 ),
    inference(avatar_split_clause,[],[f3937,f3919,f3943])).

fof(f3919,plain,
    ( spl12_381
  <=> ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_381])])).

fof(f3937,plain,
    ( ~ r1_tarski(k1_tarski(sK6(sK0,sK1,sK3)),sK1)
    | ~ spl12_381 ),
    inference(resolution,[],[f3920,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',t3_subset)).

fof(f3920,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ spl12_381 ),
    inference(avatar_component_clause,[],[f3919])).

fof(f3921,plain,
    ( ~ spl12_381
    | spl12_81
    | spl12_377 ),
    inference(avatar_split_clause,[],[f3891,f3883,f759,f3919])).

fof(f759,plain,
    ( spl12_81
  <=> k1_xboole_0 != k1_tarski(sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_81])])).

fof(f3883,plain,
    ( spl12_377
  <=> ~ r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_377])])).

fof(f3891,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ spl12_81
    | ~ spl12_377 ),
    inference(subsumption_resolution,[],[f3890,f93])).

fof(f93,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',fc1_finset_1)).

fof(f3890,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl12_81
    | ~ spl12_377 ),
    inference(subsumption_resolution,[],[f3889,f760])).

fof(f760,plain,
    ( k1_xboole_0 != k1_tarski(sK6(sK0,sK1,sK3))
    | ~ spl12_81 ),
    inference(avatar_component_clause,[],[f759])).

fof(f3889,plain,
    ( ~ m1_subset_1(k1_tarski(sK6(sK0,sK1,sK3)),k1_zfmisc_1(sK1))
    | k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | ~ v1_finset_1(k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl12_377 ),
    inference(resolution,[],[f3884,f83])).

fof(f83,plain,(
    ! [X6] :
      ( r2_yellow_0(sK0,X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
      | k1_xboole_0 = X6
      | ~ v1_finset_1(X6) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(rectify,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',t57_waybel_0)).

fof(f3884,plain,
    ( ~ r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3)))
    | ~ spl12_377 ),
    inference(avatar_component_clause,[],[f3883])).

fof(f3888,plain,
    ( ~ spl12_377
    | spl12_378
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | spl12_15
    | ~ spl12_50 ),
    inference(avatar_split_clause,[],[f2039,f468,f223,f201,f171,f164,f3886,f3883])).

fof(f164,plain,
    ( spl12_4
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f171,plain,
    ( spl12_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_6])])).

fof(f201,plain,
    ( spl12_8
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_8])])).

fof(f223,plain,
    ( spl12_15
  <=> ~ r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_15])])).

fof(f468,plain,
    ( spl12_50
  <=> m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_50])])).

fof(f2039,plain,
    ( ! [X2] :
        ( ~ r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),X2)
        | ~ r1_lattice3(sK0,X2,sK3)
        | ~ r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) )
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_15
    | ~ spl12_50 ),
    inference(subsumption_resolution,[],[f2025,f186])).

fof(f186,plain,
    ( ! [X28] : m1_subset_1(k2_yellow_0(sK0,X28),u1_struct_0(sK0))
    | ~ spl12_6 ),
    inference(resolution,[],[f172,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( l1_orders_2(X0)
     => m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',dt_k2_yellow_0)).

fof(f172,plain,
    ( l1_orders_2(sK0)
    | ~ spl12_6 ),
    inference(avatar_component_clause,[],[f171])).

fof(f2025,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),u1_struct_0(sK0))
        | ~ r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),X2)
        | ~ r1_lattice3(sK0,X2,sK3)
        | ~ r2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))) )
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_15
    | ~ spl12_50 ),
    inference(resolution,[],[f1710,f221])).

fof(f221,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2))
        | ~ r2_yellow_0(sK0,X2) )
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f219,f172])).

fof(f219,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X2)
        | r1_lattice3(sK0,X2,k2_yellow_0(sK0,X2)) )
    | ~ spl12_6 ),
    inference(resolution,[],[f186,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r1_lattice3(X0,X1,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',d10_yellow_0)).

fof(f1710,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X3)
        | ~ r1_lattice3(sK0,X3,sK3) )
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_15
    | ~ spl12_50 ),
    inference(subsumption_resolution,[],[f1706,f202])).

fof(f202,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl12_8 ),
    inference(avatar_component_clause,[],[f201])).

fof(f1706,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X2)
        | ~ r2_hidden(X2,X3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X3,sK3) )
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_15
    | ~ spl12_50 ),
    inference(duplicate_literal_removal,[],[f1697])).

fof(f1697,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,X3)
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X3,sK3) )
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_15
    | ~ spl12_50 ),
    inference(resolution,[],[f1655,f182])).

fof(f182,plain,
    ( ! [X19,X20,X18] :
        ( r1_orders_2(sK0,X18,X19)
        | ~ m1_subset_1(X19,u1_struct_0(sK0))
        | ~ r2_hidden(X19,X20)
        | ~ m1_subset_1(X18,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X20,X18) )
    | ~ spl12_6 ),
    inference(resolution,[],[f172,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X3,X1)
      | r1_orders_2(X0,X2,X3)
      | ~ r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',d8_lattice3)).

fof(f1655,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK0,sK3,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X5) )
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_15
    | ~ spl12_50 ),
    inference(subsumption_resolution,[],[f1648,f469])).

fof(f469,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl12_50 ),
    inference(avatar_component_clause,[],[f468])).

fof(f1648,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK0,sK3,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X5) )
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_15 ),
    inference(duplicate_literal_removal,[],[f1645])).

fof(f1645,plain,
    ( ! [X5] :
        ( ~ r1_orders_2(sK0,sK3,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_15 ),
    inference(resolution,[],[f1556,f177])).

fof(f177,plain,
    ( ! [X6,X7] :
        ( r1_orders_2(sK0,X6,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(X7),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0)) )
    | ~ spl12_6 ),
    inference(resolution,[],[f172,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',t7_yellow_0)).

fof(f1556,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,X1,sK6(sK0,sK1,sK3))
        | ~ r1_orders_2(sK0,sK3,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f1552,f202])).

fof(f1552,plain,
    ( ! [X1] :
        ( ~ r1_orders_2(sK0,sK3,X1)
        | ~ r1_orders_2(sK0,X1,sK6(sK0,sK1,sK3))
        | ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl12_4
    | ~ spl12_6
    | ~ spl12_15 ),
    inference(resolution,[],[f224,f445])).

fof(f445,plain,
    ( ! [X2,X0,X1] :
        ( r1_lattice3(sK0,X2,X1)
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f444,f172])).

fof(f444,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(duplicate_literal_removal,[],[f443])).

fof(f443,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X1,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X2,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X2,X1) )
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(resolution,[],[f351,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f351,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X1,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,X2) )
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(duplicate_literal_removal,[],[f350])).

fof(f350,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK6(sK0,X1,X2),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X2,X0)
        | ~ r1_orders_2(sK0,X0,sK6(sK0,X1,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_lattice3(sK0,X1,X2) )
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(resolution,[],[f190,f184])).

fof(f184,plain,
    ( ! [X24,X23] :
        ( ~ r1_orders_2(sK0,X23,sK6(sK0,X24,X23))
        | ~ m1_subset_1(X23,u1_struct_0(sK0))
        | r1_lattice3(sK0,X24,X23) )
    | ~ spl12_6 ),
    inference(resolution,[],[f172,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,sK6(X0,X1,X2))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f190,plain,
    ( ! [X26,X27,X25] :
        ( r1_orders_2(sK0,X25,X27)
        | ~ m1_subset_1(X26,u1_struct_0(sK0))
        | ~ m1_subset_1(X27,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X25,X26)
        | ~ r1_orders_2(sK0,X26,X27)
        | ~ m1_subset_1(X25,u1_struct_0(sK0)) )
    | ~ spl12_4
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f185,f165])).

fof(f165,plain,
    ( v4_orders_2(sK0)
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f164])).

fof(f185,plain,
    ( ! [X26,X27,X25] :
        ( ~ v4_orders_2(sK0)
        | ~ m1_subset_1(X25,u1_struct_0(sK0))
        | ~ m1_subset_1(X26,u1_struct_0(sK0))
        | ~ m1_subset_1(X27,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X25,X26)
        | ~ r1_orders_2(sK0,X26,X27)
        | r1_orders_2(sK0,X25,X27) )
    | ~ spl12_6 ),
    inference(resolution,[],[f172,f113])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',t26_orders_2)).

fof(f224,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ spl12_15 ),
    inference(avatar_component_clause,[],[f223])).

fof(f1620,plain,(
    ~ spl12_48 ),
    inference(avatar_contradiction_clause,[],[f1619])).

fof(f1619,plain,
    ( $false
    | ~ spl12_48 ),
    inference(subsumption_resolution,[],[f1616,f91])).

fof(f91,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',fc1_xboole_0)).

fof(f1616,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl12_48 ),
    inference(resolution,[],[f459,f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',t7_boole)).

fof(f459,plain,
    ( r2_hidden(sK6(sK0,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl12_48 ),
    inference(avatar_component_clause,[],[f458])).

fof(f458,plain,
    ( spl12_48
  <=> r2_hidden(sK6(sK0,k1_xboole_0,sK3),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_48])])).

fof(f1548,plain,
    ( ~ spl12_6
    | ~ spl12_8
    | ~ spl12_14
    | ~ spl12_32
    | ~ spl12_54
    | spl12_105 ),
    inference(avatar_contradiction_clause,[],[f1547])).

fof(f1547,plain,
    ( $false
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_14
    | ~ spl12_32
    | ~ spl12_54
    | ~ spl12_105 ),
    inference(subsumption_resolution,[],[f1546,f509])).

fof(f509,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl12_54 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl12_54
  <=> m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_54])])).

fof(f1546,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_14
    | ~ spl12_32
    | ~ spl12_105 ),
    inference(subsumption_resolution,[],[f1545,f328])).

fof(f328,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl12_32 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl12_32
  <=> r2_hidden(sK6(sK0,sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_32])])).

fof(f1545,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_14
    | ~ spl12_105 ),
    inference(subsumption_resolution,[],[f1544,f227])).

fof(f227,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl12_14 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl12_14
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_14])])).

fof(f1544,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_105 ),
    inference(resolution,[],[f1276,f76])).

fof(f76,plain,(
    ! [X4] :
      ( m1_subset_1(sK4(X4),k1_zfmisc_1(sK1))
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1276,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(sK6(sK0,sK2,sK3)),k1_zfmisc_1(X0))
        | ~ r1_lattice3(sK0,X0,sK3) )
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_105 ),
    inference(resolution,[],[f1014,f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1014,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X2)
        | ~ r1_lattice3(sK0,X2,sK3) )
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_105 ),
    inference(subsumption_resolution,[],[f1009,f202])).

fof(f1009,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X2,sK3)
        | ~ r1_tarski(sK4(sK6(sK0,sK2,sK3)),X2) )
    | ~ spl12_6
    | ~ spl12_105 ),
    inference(resolution,[],[f997,f179])).

fof(f179,plain,
    ( ! [X12,X13,X11] :
        ( r1_lattice3(sK0,X11,X13)
        | ~ m1_subset_1(X13,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X12,X13)
        | ~ r1_tarski(X11,X12) )
    | ~ spl12_6 ),
    inference(resolution,[],[f172,f100])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',t9_yellow_0)).

fof(f997,plain,
    ( ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ spl12_105 ),
    inference(avatar_component_clause,[],[f996])).

fof(f996,plain,
    ( spl12_105
  <=> ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_105])])).

fof(f998,plain,
    ( ~ spl12_105
    | ~ spl12_6
    | ~ spl12_8
    | spl12_17
    | ~ spl12_62
    | ~ spl12_86 ),
    inference(avatar_split_clause,[],[f883,f818,f654,f229,f201,f171,f996])).

fof(f229,plain,
    ( spl12_17
  <=> ~ r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_17])])).

fof(f654,plain,
    ( spl12_62
  <=> k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) = sK6(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_62])])).

fof(f818,plain,
    ( spl12_86
  <=> r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_86])])).

fof(f883,plain,
    ( ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_17
    | ~ spl12_62
    | ~ spl12_86 ),
    inference(subsumption_resolution,[],[f882,f230])).

fof(f230,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ spl12_17 ),
    inference(avatar_component_clause,[],[f229])).

fof(f882,plain,
    ( ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_62
    | ~ spl12_86 ),
    inference(subsumption_resolution,[],[f880,f202])).

fof(f880,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl12_6
    | ~ spl12_62
    | ~ spl12_86 ),
    inference(duplicate_literal_removal,[],[f877])).

fof(f877,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),sK3)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl12_6
    | ~ spl12_62
    | ~ spl12_86 ),
    inference(resolution,[],[f875,f184])).

fof(f875,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK6(sK0,sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0) )
    | ~ spl12_6
    | ~ spl12_62
    | ~ spl12_86 ),
    inference(subsumption_resolution,[],[f657,f819])).

fof(f819,plain,
    ( r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl12_86 ),
    inference(avatar_component_clause,[],[f818])).

fof(f657,plain,
    ( ! [X0] :
        ( r1_orders_2(sK0,X0,sK6(sK0,sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK6(sK0,sK2,sK3)),X0)
        | ~ r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) )
    | ~ spl12_6
    | ~ spl12_62 ),
    inference(superposition,[],[f220,f655])).

fof(f655,plain,
    ( k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) = sK6(sK0,sK2,sK3)
    | ~ spl12_62 ),
    inference(avatar_component_clause,[],[f654])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | ~ r2_yellow_0(sK0,X0) )
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f218,f172])).

fof(f218,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,X0,X1)
        | r1_orders_2(sK0,X1,k2_yellow_0(sK0,X0)) )
    | ~ spl12_6 ),
    inference(resolution,[],[f186,f144])).

fof(f144,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f834,plain,
    ( ~ spl12_32
    | ~ spl12_54
    | spl12_87 ),
    inference(avatar_contradiction_clause,[],[f833])).

fof(f833,plain,
    ( $false
    | ~ spl12_32
    | ~ spl12_54
    | ~ spl12_87 ),
    inference(subsumption_resolution,[],[f832,f509])).

fof(f832,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl12_32
    | ~ spl12_87 ),
    inference(subsumption_resolution,[],[f830,f328])).

fof(f830,plain,
    ( ~ r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl12_87 ),
    inference(resolution,[],[f822,f77])).

fof(f77,plain,(
    ! [X4] :
      ( r2_yellow_0(sK0,sK4(X4))
      | ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f822,plain,
    ( ~ r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3)))
    | ~ spl12_87 ),
    inference(avatar_component_clause,[],[f821])).

fof(f821,plain,
    ( spl12_87
  <=> ~ r2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_87])])).

fof(f765,plain,
    ( k1_xboole_0 != k1_tarski(sK6(sK0,sK1,sK3))
    | ~ r1_lattice3(sK0,k1_xboole_0,sK3)
    | r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) ),
    introduced(theory_axiom,[])).

fof(f764,plain,
    ( spl12_78
    | spl12_80
    | ~ spl12_18 ),
    inference(avatar_split_clause,[],[f556,f246,f762,f756])).

fof(f762,plain,
    ( spl12_80
  <=> k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_80])])).

fof(f556,plain,
    ( k1_xboole_0 = k1_tarski(sK6(sK0,sK1,sK3))
    | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK6(sK0,sK1,sK3))),sK2)
    | ~ spl12_18 ),
    inference(resolution,[],[f362,f247])).

fof(f362,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = k1_tarski(X0)
      | r2_hidden(k2_yellow_0(sK0,k1_tarski(X0)),sK2) ) ),
    inference(resolution,[],[f267,f123])).

fof(f267,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tarski(X0),sK1)
      | r2_hidden(k2_yellow_0(sK0,k1_tarski(X0)),sK2)
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f236,f125])).

fof(f236,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tarski(X0),k1_zfmisc_1(sK1))
      | k1_xboole_0 = k1_tarski(X0)
      | r2_hidden(k2_yellow_0(sK0,k1_tarski(X0)),sK2) ) ),
    inference(resolution,[],[f82,f93])).

fof(f82,plain,(
    ! [X3] :
      ( ~ v1_finset_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | k1_xboole_0 = X3
      | r2_hidden(k2_yellow_0(sK0,X3),sK2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f656,plain,
    ( spl12_62
    | ~ spl12_32
    | ~ spl12_54 ),
    inference(avatar_split_clause,[],[f649,f508,f327,f654])).

fof(f649,plain,
    ( k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) = sK6(sK0,sK2,sK3)
    | ~ spl12_32
    | ~ spl12_54 ),
    inference(subsumption_resolution,[],[f617,f509])).

fof(f617,plain,
    ( ~ m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | k2_yellow_0(sK0,sK4(sK6(sK0,sK2,sK3))) = sK6(sK0,sK2,sK3)
    | ~ spl12_32 ),
    inference(resolution,[],[f328,f78])).

fof(f78,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,sK2)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | k2_yellow_0(sK0,sK4(X4)) = X4 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f578,plain,
    ( ~ spl12_59
    | ~ spl12_6
    | ~ spl12_8
    | spl12_15 ),
    inference(avatar_split_clause,[],[f567,f223,f201,f171,f576])).

fof(f576,plain,
    ( spl12_59
  <=> ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_59])])).

fof(f567,plain,
    ( ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f565,f202])).

fof(f565,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,sK1,sK3)),sK3)
    | ~ spl12_6
    | ~ spl12_15 ),
    inference(resolution,[],[f408,f224])).

fof(f408,plain,
    ( ! [X0,X1] :
        ( r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1) )
    | ~ spl12_6 ),
    inference(subsumption_resolution,[],[f407,f172])).

fof(f407,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1)
        | ~ l1_orders_2(sK0) )
    | ~ spl12_6 ),
    inference(duplicate_literal_removal,[],[f406])).

fof(f406,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl12_6 ),
    inference(resolution,[],[f299,f107])).

fof(f299,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl12_6 ),
    inference(duplicate_literal_removal,[],[f298])).

fof(f298,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK6(sK0,X0,X1),u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,k1_tarski(sK6(sK0,X0,X1)),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r1_lattice3(sK0,X0,X1) )
    | ~ spl12_6 ),
    inference(resolution,[],[f177,f184])).

fof(f510,plain,
    ( spl12_54
    | ~ spl12_10
    | ~ spl12_32 ),
    inference(avatar_split_clause,[],[f503,f327,f208,f508])).

fof(f208,plain,
    ( spl12_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_10])])).

fof(f503,plain,
    ( m1_subset_1(sK6(sK0,sK2,sK3),u1_struct_0(sK0))
    | ~ spl12_10
    | ~ spl12_32 ),
    inference(resolution,[],[f483,f209])).

fof(f209,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_10 ),
    inference(avatar_component_clause,[],[f208])).

fof(f483,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X2))
        | m1_subset_1(sK6(sK0,sK2,sK3),X2) )
    | ~ spl12_32 ),
    inference(resolution,[],[f328,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/waybel_0__t57_waybel_0.p',t4_subset)).

fof(f470,plain,
    ( spl12_50
    | ~ spl12_12
    | ~ spl12_18 ),
    inference(avatar_split_clause,[],[f463,f246,f215,f468])).

fof(f215,plain,
    ( spl12_12
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_12])])).

fof(f463,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ spl12_12
    | ~ spl12_18 ),
    inference(resolution,[],[f421,f216])).

fof(f216,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl12_12 ),
    inference(avatar_component_clause,[],[f215])).

fof(f421,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(X1))
        | m1_subset_1(sK6(sK0,sK1,sK3),X1) )
    | ~ spl12_18 ),
    inference(resolution,[],[f247,f132])).

fof(f460,plain,
    ( spl12_48
    | ~ spl12_6
    | ~ spl12_8
    | spl12_27 ),
    inference(avatar_split_clause,[],[f296,f288,f201,f171,f458])).

fof(f288,plain,
    ( spl12_27
  <=> ~ r1_lattice3(sK0,k1_xboole_0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_27])])).

fof(f296,plain,
    ( r2_hidden(sK6(sK0,k1_xboole_0,sK3),k1_xboole_0)
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_27 ),
    inference(subsumption_resolution,[],[f294,f202])).

fof(f294,plain,
    ( r2_hidden(sK6(sK0,k1_xboole_0,sK3),k1_xboole_0)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl12_6
    | ~ spl12_27 ),
    inference(resolution,[],[f289,f183])).

fof(f183,plain,
    ( ! [X21,X22] :
        ( r1_lattice3(sK0,X22,X21)
        | r2_hidden(sK6(sK0,X22,X21),X22)
        | ~ m1_subset_1(X21,u1_struct_0(sK0)) )
    | ~ spl12_6 ),
    inference(resolution,[],[f172,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(sK6(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f289,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK3)
    | ~ spl12_27 ),
    inference(avatar_component_clause,[],[f288])).

fof(f329,plain,
    ( spl12_32
    | ~ spl12_6
    | ~ spl12_8
    | spl12_17 ),
    inference(avatar_split_clause,[],[f254,f229,f201,f171,f327])).

fof(f254,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_17 ),
    inference(subsumption_resolution,[],[f253,f202])).

fof(f253,plain,
    ( r2_hidden(sK6(sK0,sK2,sK3),sK2)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl12_6
    | ~ spl12_17 ),
    inference(resolution,[],[f230,f183])).

fof(f251,plain,
    ( ~ spl12_14
    | ~ spl12_16 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl12_14
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f249,f227])).

fof(f249,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ spl12_16 ),
    inference(subsumption_resolution,[],[f80,f233])).

fof(f80,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f248,plain,
    ( spl12_18
    | ~ spl12_6
    | ~ spl12_8
    | spl12_15 ),
    inference(avatar_split_clause,[],[f241,f223,f201,f171,f246])).

fof(f241,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ spl12_6
    | ~ spl12_8
    | ~ spl12_15 ),
    inference(subsumption_resolution,[],[f240,f202])).

fof(f240,plain,
    ( r2_hidden(sK6(sK0,sK1,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl12_6
    | ~ spl12_15 ),
    inference(resolution,[],[f183,f224])).

fof(f234,plain,
    ( spl12_14
    | spl12_16 ),
    inference(avatar_split_clause,[],[f79,f232,f226])).

fof(f79,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f217,plain,(
    spl12_12 ),
    inference(avatar_split_clause,[],[f85,f215])).

fof(f85,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f210,plain,(
    spl12_10 ),
    inference(avatar_split_clause,[],[f84,f208])).

fof(f84,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f43])).

fof(f203,plain,(
    spl12_8 ),
    inference(avatar_split_clause,[],[f81,f201])).

fof(f81,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f173,plain,(
    spl12_6 ),
    inference(avatar_split_clause,[],[f89,f171])).

fof(f89,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f166,plain,(
    spl12_4 ),
    inference(avatar_split_clause,[],[f88,f164])).

fof(f88,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
