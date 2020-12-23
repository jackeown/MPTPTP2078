%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  228 ( 692 expanded)
%              Number of leaves         :   39 ( 247 expanded)
%              Depth                    :   20
%              Number of atoms          : 1017 (3757 expanded)
%              Number of equality atoms :   57 ( 254 expanded)
%              Maximal formula depth    :   19 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1562,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f72,f76,f80,f123,f220,f240,f257,f277,f309,f333,f410,f419,f423,f456,f495,f503,f542,f559,f572,f785,f845,f893,f933,f957,f992,f1013,f1222,f1537,f1561])).

fof(f1561,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | spl7_97 ),
    inference(avatar_contradiction_clause,[],[f1560])).

fof(f1560,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | spl7_97 ),
    inference(subsumption_resolution,[],[f1559,f131])).

fof(f131,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | spl7_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl7_9
  <=> r1_lattice3(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f1559,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_97 ),
    inference(resolution,[],[f1536,f213])).

fof(f213,plain,
    ( ! [X1] :
        ( r1_lattice3(sK0,k1_tarski(sK5(sK0,X1,sK3)),sK5(sK0,X1,sK3))
        | r1_lattice3(sK0,X1,sK3) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f212,f89])).

fof(f89,plain,
    ( ! [X2] :
        ( m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,sK3) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f83,f75])).

fof(f75,plain,
    ( l1_orders_2(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl7_3
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f83,plain,
    ( ! [X2] :
        ( ~ l1_orders_2(sK0)
        | m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0))
        | r1_lattice3(sK0,X2,sK3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f79,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X2,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).

fof(f79,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl7_4
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f212,plain,
    ( ! [X1] :
        ( r1_lattice3(sK0,X1,sK3)
        | ~ m1_subset_1(sK5(sK0,X1,sK3),u1_struct_0(sK0))
        | r1_lattice3(sK0,k1_tarski(sK5(sK0,X1,sK3)),sK5(sK0,X1,sK3)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f208,f75])).

fof(f208,plain,
    ( ! [X1] :
        ( r1_lattice3(sK0,X1,sK3)
        | ~ m1_subset_1(sK5(sK0,X1,sK3),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,k1_tarski(sK5(sK0,X1,sK3)),sK5(sK0,X1,sK3)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,
    ( ! [X1] :
        ( r1_lattice3(sK0,X1,sK3)
        | ~ m1_subset_1(sK5(sK0,X1,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(sK5(sK0,X1,sK3),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,k1_tarski(sK5(sK0,X1,sK3)),sK5(sK0,X1,sK3)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f181,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,k1_tarski(X2),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).

fof(f181,plain,
    ( ! [X4] :
        ( r1_orders_2(sK0,sK5(sK0,X4,sK3),sK5(sK0,X4,sK3))
        | r1_lattice3(sK0,X4,sK3) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f180,f67])).

fof(f67,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f180,plain,
    ( ! [X4] :
        ( r1_lattice3(sK0,X4,sK3)
        | v2_struct_0(sK0)
        | r1_orders_2(sK0,sK5(sK0,X4,sK3),sK5(sK0,X4,sK3)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f179,f75])).

fof(f179,plain,
    ( ! [X4] :
        ( r1_lattice3(sK0,X4,sK3)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | r1_orders_2(sK0,sK5(sK0,X4,sK3),sK5(sK0,X4,sK3)) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f175,f71])).

fof(f71,plain,
    ( v3_orders_2(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl7_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f175,plain,
    ( ! [X4] :
        ( r1_lattice3(sK0,X4,sK3)
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0)
        | r1_orders_2(sK0,sK5(sK0,X4,sK3),sK5(sK0,X4,sK3)) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f89,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_orders_2(X0,X1,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

fof(f1536,plain,
    ( ~ r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))
    | spl7_97 ),
    inference(avatar_component_clause,[],[f1535])).

fof(f1535,plain,
    ( spl7_97
  <=> r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).

fof(f1537,plain,
    ( spl7_60
    | ~ spl7_97
    | ~ spl7_68
    | ~ spl7_3
    | ~ spl7_19
    | ~ spl7_78 ),
    inference(avatar_split_clause,[],[f1232,f1220,f215,f74,f871,f1535,f780])).

fof(f780,plain,
    ( spl7_60
  <=> sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f871,plain,
    ( spl7_68
  <=> m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).

fof(f215,plain,
    ( spl7_19
  <=> r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f1220,plain,
    ( spl7_78
  <=> r1_orders_2(sK0,sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).

fof(f1232,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))
    | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_3
    | ~ spl7_19
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f1231,f75])).

fof(f1231,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))
    | ~ l1_orders_2(sK0)
    | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_19
    | ~ spl7_78 ),
    inference(subsumption_resolution,[],[f1228,f216])).

fof(f216,plain,
    ( r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f215])).

fof(f1228,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))
    | ~ l1_orders_2(sK0)
    | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_78 ),
    inference(resolution,[],[f1221,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f1221,plain,
    ( r1_orders_2(sK0,sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))
    | ~ spl7_78 ),
    inference(avatar_component_clause,[],[f1220])).

fof(f1222,plain,
    ( spl7_78
    | ~ spl7_68
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f970,f955,f783,f74,f871,f1220])).

fof(f783,plain,
    ( spl7_61
  <=> m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).

fof(f955,plain,
    ( spl7_71
  <=> r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f970,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))
    | ~ spl7_3
    | ~ spl7_61
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f969,f75])).

fof(f969,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))
    | ~ spl7_61
    | ~ spl7_71 ),
    inference(subsumption_resolution,[],[f961,f784])).

fof(f784,plain,
    ( m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),u1_struct_0(sK0))
    | ~ spl7_61 ),
    inference(avatar_component_clause,[],[f783])).

fof(f961,plain,
    ( ~ m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))
    | ~ spl7_71 ),
    inference(resolution,[],[f956,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,k1_tarski(X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f956,plain,
    ( r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)))
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f955])).

fof(f1013,plain,
    ( spl7_69
    | ~ spl7_68
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_72 ),
    inference(avatar_split_clause,[],[f1003,f990,f78,f74,f871,f923])).

fof(f923,plain,
    ( spl7_69
  <=> r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).

fof(f990,plain,
    ( spl7_72
  <=> r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).

fof(f1003,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f1002,f75])).

fof(f1002,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_4
    | ~ spl7_72 ),
    inference(subsumption_resolution,[],[f996,f79])).

fof(f996,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_72 ),
    inference(resolution,[],[f991,f59])).

fof(f991,plain,
    ( r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3)
    | ~ spl7_72 ),
    inference(avatar_component_clause,[],[f990])).

fof(f992,plain,
    ( spl7_72
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_65 ),
    inference(avatar_split_clause,[],[f984,f843,f121,f78,f74,f990])).

fof(f121,plain,
    ( spl7_10
  <=> r1_lattice3(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f843,plain,
    ( spl7_65
  <=> r1_tarski(k1_tarski(sK5(sK0,sK1,sK3)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).

fof(f984,plain,
    ( r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_65 ),
    inference(subsumption_resolution,[],[f983,f75])).

fof(f983,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3)
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_65 ),
    inference(subsumption_resolution,[],[f981,f79])).

fof(f981,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3)
    | ~ spl7_10
    | ~ spl7_65 ),
    inference(resolution,[],[f851,f122])).

fof(f122,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f851,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice3(X2,sK2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ l1_orders_2(X2)
        | r1_lattice3(X2,k1_tarski(sK5(sK0,sK1,sK3)),X3) )
    | ~ spl7_65 ),
    inference(resolution,[],[f844,f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X2,X3)
      | r1_lattice3(X0,X1,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).

fof(f844,plain,
    ( r1_tarski(k1_tarski(sK5(sK0,sK1,sK3)),sK2)
    | ~ spl7_65 ),
    inference(avatar_component_clause,[],[f843])).

fof(f957,plain,
    ( spl7_60
    | spl7_71
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f629,f215,f118,f78,f74,f70,f66,f955,f780])).

fof(f629,plain,
    ( r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)))
    | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f628,f131])).

fof(f628,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)))
    | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_19 ),
    inference(resolution,[],[f234,f216])).

fof(f234,plain,
    ( ! [X3] :
        ( ~ r2_yellow_0(sK0,k1_tarski(sK5(sK0,X3,sK3)))
        | r1_lattice3(sK0,X3,sK3)
        | r1_lattice3(sK0,k1_tarski(sK5(sK0,X3,sK3)),sK6(sK0,k1_tarski(sK5(sK0,X3,sK3)),sK5(sK0,X3,sK3)))
        | sK5(sK0,X3,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,X3,sK3))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f233,f89])).

fof(f233,plain,
    ( ! [X3] :
        ( r1_lattice3(sK0,X3,sK3)
        | ~ m1_subset_1(sK5(sK0,X3,sK3),u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,k1_tarski(sK5(sK0,X3,sK3)))
        | r1_lattice3(sK0,k1_tarski(sK5(sK0,X3,sK3)),sK6(sK0,k1_tarski(sK5(sK0,X3,sK3)),sK5(sK0,X3,sK3)))
        | sK5(sK0,X3,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,X3,sK3))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f228,f75])).

fof(f228,plain,
    ( ! [X3] :
        ( r1_lattice3(sK0,X3,sK3)
        | ~ m1_subset_1(sK5(sK0,X3,sK3),u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,k1_tarski(sK5(sK0,X3,sK3)))
        | ~ l1_orders_2(sK0)
        | r1_lattice3(sK0,k1_tarski(sK5(sK0,X3,sK3)),sK6(sK0,k1_tarski(sK5(sK0,X3,sK3)),sK5(sK0,X3,sK3)))
        | sK5(sK0,X3,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,X3,sK3))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f213,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,sK6(X0,X1,X2))
      | k2_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f933,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | ~ spl7_69 ),
    inference(avatar_contradiction_clause,[],[f932])).

fof(f932,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f931,f131])).

fof(f931,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f930,f75])).

fof(f930,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_4
    | ~ spl7_69 ),
    inference(subsumption_resolution,[],[f927,f79])).

fof(f927,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_69 ),
    inference(resolution,[],[f924,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f924,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))
    | ~ spl7_69 ),
    inference(avatar_component_clause,[],[f923])).

fof(f893,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | spl7_68 ),
    inference(avatar_contradiction_clause,[],[f892])).

fof(f892,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | spl7_68 ),
    inference(subsumption_resolution,[],[f891,f131])).

fof(f891,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_68 ),
    inference(resolution,[],[f872,f89])).

fof(f872,plain,
    ( ~ m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))
    | spl7_68 ),
    inference(avatar_component_clause,[],[f871])).

fof(f845,plain,
    ( spl7_65
    | ~ spl7_24
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f788,f780,f307,f843])).

fof(f307,plain,
    ( spl7_24
  <=> r1_tarski(k1_tarski(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f788,plain,
    ( r1_tarski(k1_tarski(sK5(sK0,sK1,sK3)),sK2)
    | ~ spl7_24
    | ~ spl7_60 ),
    inference(superposition,[],[f308,f781])).

fof(f781,plain,
    ( sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f780])).

fof(f308,plain,
    ( r1_tarski(k1_tarski(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),sK2)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f307])).

fof(f785,plain,
    ( spl7_60
    | spl7_61
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f623,f215,f118,f78,f74,f70,f66,f783,f780])).

fof(f623,plain,
    ( m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),u1_struct_0(sK0))
    | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f622,f131])).

fof(f622,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),u1_struct_0(sK0))
    | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_19 ),
    inference(resolution,[],[f232,f216])).

fof(f232,plain,
    ( ! [X2] :
        ( ~ r2_yellow_0(sK0,k1_tarski(sK5(sK0,X2,sK3)))
        | r1_lattice3(sK0,X2,sK3)
        | m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,X2,sK3)),sK5(sK0,X2,sK3)),u1_struct_0(sK0))
        | sK5(sK0,X2,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,X2,sK3))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f231,f89])).

fof(f231,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,X2,sK3)
        | ~ m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,k1_tarski(sK5(sK0,X2,sK3)))
        | m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,X2,sK3)),sK5(sK0,X2,sK3)),u1_struct_0(sK0))
        | sK5(sK0,X2,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,X2,sK3))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f227,f75])).

fof(f227,plain,
    ( ! [X2] :
        ( r1_lattice3(sK0,X2,sK3)
        | ~ m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,k1_tarski(sK5(sK0,X2,sK3)))
        | ~ l1_orders_2(sK0)
        | m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,X2,sK3)),sK5(sK0,X2,sK3)),u1_struct_0(sK0))
        | sK5(sK0,X2,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,X2,sK3))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f213,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f572,plain,
    ( ~ spl7_9
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f124,f121,f118])).

fof(f124,plain,
    ( ~ r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f33,f122])).

fof(f33,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | ~ r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

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
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
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
    inference(pure_predicate_removal,[],[f13])).

fof(f13,plain,(
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
    inference(rectify,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).

fof(f559,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | spl7_10
    | ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f558])).

fof(f558,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_4
    | spl7_10
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f557,f290])).

fof(f290,plain,
    ( ~ r1_lattice3(sK0,sK2,sK3)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f557,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f556,f75])).

fof(f556,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_4
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f553,f79])).

fof(f553,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_44 ),
    inference(resolution,[],[f541,f45])).

fof(f541,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f540])).

fof(f540,plain,
    ( spl7_44
  <=> r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f542,plain,
    ( spl7_44
    | ~ spl7_4
    | ~ spl7_42
    | ~ spl7_43 ),
    inference(avatar_split_clause,[],[f515,f501,f493,f78,f540])).

fof(f493,plain,
    ( spl7_42
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_orders_2(sK0,X0,sK5(sK0,sK2,sK3))
        | ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f501,plain,
    ( spl7_43
  <=> r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f515,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3))
    | ~ spl7_4
    | ~ spl7_42
    | ~ spl7_43 ),
    inference(subsumption_resolution,[],[f509,f79])).

fof(f509,plain,
    ( r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl7_42
    | ~ spl7_43 ),
    inference(resolution,[],[f502,f494])).

fof(f494,plain,
    ( ! [X0] :
        ( ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X0)
        | r1_orders_2(sK0,X0,sK5(sK0,sK2,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_42 ),
    inference(avatar_component_clause,[],[f493])).

fof(f502,plain,
    ( r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f501])).

fof(f503,plain,
    ( spl7_43
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f498,f417,f118,f78,f74,f501])).

fof(f417,plain,
    ( spl7_34
  <=> r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f498,plain,
    ( r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f497,f75])).

fof(f497,plain,
    ( ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_4
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(subsumption_resolution,[],[f496,f79])).

fof(f496,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)
    | ~ spl7_9
    | ~ spl7_34 ),
    inference(resolution,[],[f425,f119])).

fof(f119,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f425,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice3(X2,sK1,X3)
        | ~ m1_subset_1(X3,u1_struct_0(X2))
        | ~ l1_orders_2(X2)
        | r1_lattice3(X2,sK4(sK5(sK0,sK2,sK3)),X3) )
    | ~ spl7_34 ),
    inference(resolution,[],[f418,f62])).

fof(f418,plain,
    ( r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1)
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f417])).

fof(f495,plain,
    ( spl7_42
    | ~ spl7_39
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f429,f421,f331,f74,f451,f493])).

fof(f451,plain,
    ( spl7_39
  <=> m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f331,plain,
    ( spl7_28
  <=> r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f421,plain,
    ( spl7_35
  <=> sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f429,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X0)
        | r1_orders_2(sK0,X0,sK5(sK0,sK2,sK3)) )
    | ~ spl7_3
    | ~ spl7_28
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f428,f332])).

fof(f332,plain,
    ( r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f331])).

fof(f428,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
        | ~ r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X0)
        | r1_orders_2(sK0,X0,sK5(sK0,sK2,sK3)) )
    | ~ spl7_3
    | ~ spl7_35 ),
    inference(subsumption_resolution,[],[f426,f75])).

fof(f426,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X0)
        | r1_orders_2(sK0,X0,sK5(sK0,sK2,sK3)) )
    | ~ spl7_35 ),
    inference(superposition,[],[f64,f422])).

fof(f422,plain,
    ( sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f421])).

fof(f64,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,k2_yellow_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X3)
      | r1_orders_2(X0,X3,X2)
      | k2_yellow_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f456,plain,
    ( ~ spl7_3
    | ~ spl7_4
    | spl7_10
    | spl7_39 ),
    inference(avatar_contradiction_clause,[],[f455])).

fof(f455,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_4
    | spl7_10
    | spl7_39 ),
    inference(subsumption_resolution,[],[f454,f290])).

fof(f454,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_39 ),
    inference(resolution,[],[f452,f89])).

fof(f452,plain,
    ( ~ m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))
    | spl7_39 ),
    inference(avatar_component_clause,[],[f451])).

fof(f423,plain,
    ( spl7_35
    | ~ spl7_3
    | ~ spl7_4
    | spl7_10 ),
    inference(avatar_split_clause,[],[f402,f121,f78,f74,f421])).

fof(f402,plain,
    ( sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f302,f290])).

fof(f302,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f301])).

fof(f301,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f171,f90])).

fof(f90,plain,
    ( ! [X3] :
        ( r2_hidden(sK5(sK0,X3,sK3),X3)
        | r1_lattice3(sK0,X3,sK3) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f84,f75])).

fof(f84,plain,
    ( ! [X3] :
        ( ~ l1_orders_2(sK0)
        | r2_hidden(sK5(sK0,X3,sK3),X3)
        | r1_lattice3(sK0,X3,sK3) )
    | ~ spl7_4 ),
    inference(resolution,[],[f79,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_hidden(sK5(X0,X1,X2),X1)
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f171,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(sK0,X0,sK3),sK2)
        | r1_lattice3(sK0,X0,sK3)
        | sK5(sK0,X0,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,X0,sK3))) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f89,f31])).

fof(f31,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | k2_yellow_0(sK0,sK4(X4)) = X4 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f419,plain,
    ( spl7_34
    | ~ spl7_33 ),
    inference(avatar_split_clause,[],[f413,f408,f417])).

fof(f408,plain,
    ( spl7_33
  <=> m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).

fof(f413,plain,
    ( r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1)
    | ~ spl7_33 ),
    inference(resolution,[],[f409,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f409,plain,
    ( m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_33 ),
    inference(avatar_component_clause,[],[f408])).

fof(f410,plain,
    ( spl7_33
    | ~ spl7_3
    | ~ spl7_4
    | spl7_10 ),
    inference(avatar_split_clause,[],[f401,f121,f78,f74,f408])).

fof(f401,plain,
    ( m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_3
    | ~ spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f242,f290])).

fof(f242,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f172,f90])).

fof(f172,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK5(sK0,X1,sK3),sK2)
        | r1_lattice3(sK0,X1,sK3)
        | m1_subset_1(sK4(sK5(sK0,X1,sK3)),k1_zfmisc_1(sK1)) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f89,f29])).

fof(f29,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | m1_subset_1(sK4(X4),k1_zfmisc_1(sK1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f333,plain,
    ( spl7_28
    | ~ spl7_3
    | ~ spl7_4
    | spl7_10 ),
    inference(avatar_split_clause,[],[f310,f121,f78,f74,f331])).

fof(f310,plain,
    ( r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f236,f290])).

fof(f236,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))
    | r1_lattice3(sK0,sK2,sK3)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f173,f90])).

fof(f173,plain,
    ( ! [X2] :
        ( ~ r2_hidden(sK5(sK0,X2,sK3),sK2)
        | r1_lattice3(sK0,X2,sK3)
        | r2_yellow_0(sK0,sK4(sK5(sK0,X2,sK3))) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f89,f30])).

fof(f30,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | r2_yellow_0(sK0,sK4(X4)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f309,plain,
    ( spl7_24
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f303,f275,f307])).

fof(f275,plain,
    ( spl7_22
  <=> m1_subset_1(k1_tarski(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f303,plain,
    ( r1_tarski(k1_tarski(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),sK2)
    | ~ spl7_22 ),
    inference(resolution,[],[f276,f54])).

fof(f276,plain,
    ( m1_subset_1(k1_tarski(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),k1_zfmisc_1(sK2))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f275])).

fof(f277,plain,
    ( spl7_22
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f259,f238,f275])).

fof(f238,plain,
    ( spl7_21
  <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f259,plain,
    ( m1_subset_1(k1_tarski(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),k1_zfmisc_1(sK2))
    | ~ spl7_21 ),
    inference(resolution,[],[f239,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f239,plain,
    ( r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f238])).

fof(f257,plain,(
    ~ spl7_20 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl7_20 ),
    inference(subsumption_resolution,[],[f248,f52])).

fof(f52,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f248,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_20 ),
    inference(superposition,[],[f60,f219])).

fof(f219,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f218])).

fof(f218,plain,
    ( spl7_20
  <=> k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f60,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f240,plain,
    ( spl7_21
    | spl7_20
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9 ),
    inference(avatar_split_clause,[],[f189,f118,f78,f74,f218,f238])).

fof(f189,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9 ),
    inference(subsumption_resolution,[],[f188,f53])).

fof(f53,plain,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_finset_1(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).

fof(f188,plain,
    ( ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9 ),
    inference(subsumption_resolution,[],[f186,f131])).

fof(f186,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f162,f35])).

fof(f35,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X3)
      | k1_xboole_0 = X3
      | r2_hidden(k2_yellow_0(sK0,X3),sK2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f162,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_tarski(sK5(sK0,X0,sK3)),k1_zfmisc_1(X0))
        | r1_lattice3(sK0,X0,sK3) )
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f90,f51])).

fof(f220,plain,
    ( spl7_19
    | spl7_20
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9 ),
    inference(avatar_split_clause,[],[f191,f118,f78,f74,f218,f215])).

fof(f191,plain,
    ( k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9 ),
    inference(subsumption_resolution,[],[f190,f53])).

fof(f190,plain,
    ( ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9 ),
    inference(subsumption_resolution,[],[f187,f131])).

fof(f187,plain,
    ( r1_lattice3(sK0,sK1,sK3)
    | ~ v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3)))
    | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))
    | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f162,f36])).

fof(f36,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(sK1))
      | ~ v1_finset_1(X6)
      | k1_xboole_0 = X6
      | r2_yellow_0(sK0,X6) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f123,plain,
    ( spl7_9
    | spl7_10 ),
    inference(avatar_split_clause,[],[f32,f121,f118])).

fof(f32,plain,
    ( r1_lattice3(sK0,sK2,sK3)
    | r1_lattice3(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f34,f78])).

fof(f34,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f41,f74])).

fof(f41,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f40,f70])).

fof(f40,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f39,f66])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:31:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (20011)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.46  % (20027)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (20017)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (20016)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (20026)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (20014)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (20012)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (20018)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (20013)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (20024)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (20015)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (20022)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (20025)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (20023)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (20031)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (20028)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (20030)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (20021)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (20029)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (20020)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (20019)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.54  % (20011)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f1562,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f68,f72,f76,f80,f123,f220,f240,f257,f277,f309,f333,f410,f419,f423,f456,f495,f503,f542,f559,f572,f785,f845,f893,f933,f957,f992,f1013,f1222,f1537,f1561])).
% 0.21/0.56  fof(f1561,plain,(
% 0.21/0.56    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_9 | spl7_97),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f1560])).
% 0.21/0.56  fof(f1560,plain,(
% 0.21/0.56    $false | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_9 | spl7_97)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1559,f131])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    ~r1_lattice3(sK0,sK1,sK3) | spl7_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f118])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    spl7_9 <=> r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.56  fof(f1559,plain,(
% 0.21/0.56    r1_lattice3(sK0,sK1,sK3) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_97)),
% 0.21/0.56    inference(resolution,[],[f1536,f213])).
% 0.21/0.56  fof(f213,plain,(
% 0.21/0.56    ( ! [X1] : (r1_lattice3(sK0,k1_tarski(sK5(sK0,X1,sK3)),sK5(sK0,X1,sK3)) | r1_lattice3(sK0,X1,sK3)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f212,f89])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X2] : (m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0)) | r1_lattice3(sK0,X2,sK3)) ) | (~spl7_3 | ~spl7_4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f83,f75])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    l1_orders_2(sK0) | ~spl7_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    spl7_3 <=> l1_orders_2(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X2] : (~l1_orders_2(sK0) | m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0)) | r1_lattice3(sK0,X2,sK3)) ) | ~spl7_4),
% 0.21/0.56    inference(resolution,[],[f79,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(flattening,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_lattice3)).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    m1_subset_1(sK3,u1_struct_0(sK0)) | ~spl7_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f78])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    spl7_4 <=> m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.56  fof(f212,plain,(
% 0.21/0.56    ( ! [X1] : (r1_lattice3(sK0,X1,sK3) | ~m1_subset_1(sK5(sK0,X1,sK3),u1_struct_0(sK0)) | r1_lattice3(sK0,k1_tarski(sK5(sK0,X1,sK3)),sK5(sK0,X1,sK3))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f208,f75])).
% 0.21/0.56  fof(f208,plain,(
% 0.21/0.56    ( ! [X1] : (r1_lattice3(sK0,X1,sK3) | ~m1_subset_1(sK5(sK0,X1,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,k1_tarski(sK5(sK0,X1,sK3)),sK5(sK0,X1,sK3))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f207])).
% 0.21/0.56  fof(f207,plain,(
% 0.21/0.56    ( ! [X1] : (r1_lattice3(sK0,X1,sK3) | ~m1_subset_1(sK5(sK0,X1,sK3),u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,X1,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,k1_tarski(sK5(sK0,X1,sK3)),sK5(sK0,X1,sK3))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.56    inference(resolution,[],[f181,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,k1_tarski(X2),X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (((r2_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X2,X1) | ~r2_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r1_lattice3(X0,k1_tarski(X2),X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X1) => r2_lattice3(X0,k1_tarski(X2),X1)) & (r2_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X2,X1)) & (r1_orders_2(X0,X1,X2) => r1_lattice3(X0,k1_tarski(X2),X1)) & (r1_lattice3(X0,k1_tarski(X2),X1) => r1_orders_2(X0,X1,X2))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_yellow_0)).
% 0.21/0.56  fof(f181,plain,(
% 0.21/0.56    ( ! [X4] : (r1_orders_2(sK0,sK5(sK0,X4,sK3),sK5(sK0,X4,sK3)) | r1_lattice3(sK0,X4,sK3)) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f180,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ~v2_struct_0(sK0) | spl7_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    spl7_1 <=> v2_struct_0(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.56  fof(f180,plain,(
% 0.21/0.56    ( ! [X4] : (r1_lattice3(sK0,X4,sK3) | v2_struct_0(sK0) | r1_orders_2(sK0,sK5(sK0,X4,sK3),sK5(sK0,X4,sK3))) ) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f179,f75])).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    ( ! [X4] : (r1_lattice3(sK0,X4,sK3) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_orders_2(sK0,sK5(sK0,X4,sK3),sK5(sK0,X4,sK3))) ) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.56    inference(subsumption_resolution,[],[f175,f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    v3_orders_2(sK0) | ~spl7_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f70])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    spl7_2 <=> v3_orders_2(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.56  fof(f175,plain,(
% 0.21/0.56    ( ! [X4] : (r1_lattice3(sK0,X4,sK3) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_orders_2(sK0,sK5(sK0,X4,sK3),sK5(sK0,X4,sK3))) ) | (~spl7_3 | ~spl7_4)),
% 0.21/0.56    inference(resolution,[],[f89,f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,X1,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 0.21/0.56  fof(f1536,plain,(
% 0.21/0.56    ~r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)) | spl7_97),
% 0.21/0.56    inference(avatar_component_clause,[],[f1535])).
% 0.21/0.56  fof(f1535,plain,(
% 0.21/0.56    spl7_97 <=> r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_97])])).
% 0.21/0.56  fof(f1537,plain,(
% 0.21/0.56    spl7_60 | ~spl7_97 | ~spl7_68 | ~spl7_3 | ~spl7_19 | ~spl7_78),
% 0.21/0.56    inference(avatar_split_clause,[],[f1232,f1220,f215,f74,f871,f1535,f780])).
% 0.21/0.56  fof(f780,plain,(
% 0.21/0.56    spl7_60 <=> sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 0.21/0.56  fof(f871,plain,(
% 0.21/0.56    spl7_68 <=> m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_68])])).
% 0.21/0.56  fof(f215,plain,(
% 0.21/0.56    spl7_19 <=> r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.56  fof(f1220,plain,(
% 0.21/0.56    spl7_78 <=> r1_orders_2(sK0,sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_78])])).
% 0.21/0.56  fof(f1232,plain,(
% 0.21/0.56    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)) | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (~spl7_3 | ~spl7_19 | ~spl7_78)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1231,f75])).
% 0.21/0.56  fof(f1231,plain,(
% 0.21/0.56    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)) | ~l1_orders_2(sK0) | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (~spl7_19 | ~spl7_78)),
% 0.21/0.56    inference(subsumption_resolution,[],[f1228,f216])).
% 0.21/0.56  fof(f216,plain,(
% 0.21/0.56    r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | ~spl7_19),
% 0.21/0.56    inference(avatar_component_clause,[],[f215])).
% 0.21/0.56  fof(f1228,plain,(
% 0.21/0.56    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | ~r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)) | ~l1_orders_2(sK0) | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | ~spl7_78),
% 0.21/0.56    inference(resolution,[],[f1221,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK6(X0,X1,X2),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~r1_lattice3(X0,X1,X2) | ~l1_orders_2(X0) | k2_yellow_0(X0,X1) = X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : ((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(flattening,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : (((k2_yellow_0(X0,X1) = X2 <=> (! [X3] : ((r1_orders_2(X0,X3,X2) | ~r1_lattice3(X0,X1,X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r1_lattice3(X0,X1,X2))) | ~r2_yellow_0(X0,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_yellow_0(X0,X1) => (k2_yellow_0(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) => r1_orders_2(X0,X3,X2))) & r1_lattice3(X0,X1,X2))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).
% 0.21/0.56  fof(f1221,plain,(
% 0.21/0.56    r1_orders_2(sK0,sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)) | ~spl7_78),
% 0.21/0.56    inference(avatar_component_clause,[],[f1220])).
% 0.21/0.56  fof(f1222,plain,(
% 0.21/0.56    spl7_78 | ~spl7_68 | ~spl7_3 | ~spl7_61 | ~spl7_71),
% 0.21/0.56    inference(avatar_split_clause,[],[f970,f955,f783,f74,f871,f1220])).
% 0.21/0.56  fof(f783,plain,(
% 0.21/0.56    spl7_61 <=> m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),u1_struct_0(sK0))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_61])])).
% 0.21/0.56  fof(f955,plain,(
% 0.21/0.56    spl7_71 <=> r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).
% 0.21/0.56  fof(f970,plain,(
% 0.21/0.56    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | r1_orders_2(sK0,sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)) | (~spl7_3 | ~spl7_61 | ~spl7_71)),
% 0.21/0.56    inference(subsumption_resolution,[],[f969,f75])).
% 0.21/0.56  fof(f969,plain,(
% 0.21/0.56    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)) | (~spl7_61 | ~spl7_71)),
% 0.21/0.56    inference(subsumption_resolution,[],[f961,f784])).
% 0.21/0.56  fof(f784,plain,(
% 0.21/0.56    m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),u1_struct_0(sK0)) | ~spl7_61),
% 0.21/0.56    inference(avatar_component_clause,[],[f783])).
% 0.21/0.56  fof(f961,plain,(
% 0.21/0.56    ~m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)) | ~spl7_71),
% 0.21/0.56    inference(resolution,[],[f956,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_lattice3(X0,k1_tarski(X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_orders_2(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f956,plain,(
% 0.21/0.56    r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))) | ~spl7_71),
% 0.21/0.56    inference(avatar_component_clause,[],[f955])).
% 0.21/0.56  fof(f1013,plain,(
% 0.21/0.56    spl7_69 | ~spl7_68 | ~spl7_3 | ~spl7_4 | ~spl7_72),
% 0.21/0.56    inference(avatar_split_clause,[],[f1003,f990,f78,f74,f871,f923])).
% 0.21/0.56  fof(f923,plain,(
% 0.21/0.56    spl7_69 <=> r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_69])])).
% 0.21/0.56  fof(f990,plain,(
% 0.21/0.56    spl7_72 <=> r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl7_72])])).
% 0.21/0.57  fof(f1003,plain,(
% 0.21/0.57    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) | (~spl7_3 | ~spl7_4 | ~spl7_72)),
% 0.21/0.57    inference(subsumption_resolution,[],[f1002,f75])).
% 0.21/0.57  fof(f1002,plain,(
% 0.21/0.57    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) | (~spl7_4 | ~spl7_72)),
% 0.21/0.57    inference(subsumption_resolution,[],[f996,f79])).
% 0.21/0.57  fof(f996,plain,(
% 0.21/0.57    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) | ~spl7_72),
% 0.21/0.57    inference(resolution,[],[f991,f59])).
% 0.21/0.57  fof(f991,plain,(
% 0.21/0.57    r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3) | ~spl7_72),
% 0.21/0.57    inference(avatar_component_clause,[],[f990])).
% 0.21/0.57  fof(f992,plain,(
% 0.21/0.57    spl7_72 | ~spl7_3 | ~spl7_4 | ~spl7_10 | ~spl7_65),
% 0.21/0.57    inference(avatar_split_clause,[],[f984,f843,f121,f78,f74,f990])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    spl7_10 <=> r1_lattice3(sK0,sK2,sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.57  fof(f843,plain,(
% 0.21/0.57    spl7_65 <=> r1_tarski(k1_tarski(sK5(sK0,sK1,sK3)),sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_65])])).
% 0.21/0.57  fof(f984,plain,(
% 0.21/0.57    r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3) | (~spl7_3 | ~spl7_4 | ~spl7_10 | ~spl7_65)),
% 0.21/0.57    inference(subsumption_resolution,[],[f983,f75])).
% 0.21/0.57  fof(f983,plain,(
% 0.21/0.57    ~l1_orders_2(sK0) | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3) | (~spl7_4 | ~spl7_10 | ~spl7_65)),
% 0.21/0.57    inference(subsumption_resolution,[],[f981,f79])).
% 0.21/0.57  fof(f981,plain,(
% 0.21/0.57    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK3) | (~spl7_10 | ~spl7_65)),
% 0.21/0.57    inference(resolution,[],[f851,f122])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK2,sK3) | ~spl7_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f121])).
% 0.21/0.57  fof(f851,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r1_lattice3(X2,sK2,X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2) | r1_lattice3(X2,k1_tarski(sK5(sK0,sK1,sK3)),X3)) ) | ~spl7_65),
% 0.21/0.57    inference(resolution,[],[f844,f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r1_tarski(X1,X2) | ~l1_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_lattice3(X0,X2,X3) | r1_lattice3(X0,X1,X3)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : (! [X1,X2] : (! [X3] : (((r2_lattice3(X0,X1,X3) | ~r2_lattice3(X0,X2,X3)) & (r1_lattice3(X0,X1,X3) | ~r1_lattice3(X0,X2,X3))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_tarski(X1,X2)) | ~l1_orders_2(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f10])).
% 0.21/0.57  fof(f10,axiom,(
% 0.21/0.57    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (r1_tarski(X1,X2) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r2_lattice3(X0,X2,X3) => r2_lattice3(X0,X1,X3)) & (r1_lattice3(X0,X2,X3) => r1_lattice3(X0,X1,X3))))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_yellow_0)).
% 0.21/0.57  fof(f844,plain,(
% 0.21/0.57    r1_tarski(k1_tarski(sK5(sK0,sK1,sK3)),sK2) | ~spl7_65),
% 0.21/0.57    inference(avatar_component_clause,[],[f843])).
% 0.21/0.57  fof(f957,plain,(
% 0.21/0.57    spl7_60 | spl7_71 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_9 | ~spl7_19),
% 0.21/0.57    inference(avatar_split_clause,[],[f629,f215,f118,f78,f74,f70,f66,f955,f780])).
% 0.21/0.57  fof(f629,plain,(
% 0.21/0.57    r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))) | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_9 | ~spl7_19)),
% 0.21/0.57    inference(subsumption_resolution,[],[f628,f131])).
% 0.21/0.57  fof(f628,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK1,sK3) | r1_lattice3(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3))) | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_19)),
% 0.21/0.57    inference(resolution,[],[f234,f216])).
% 0.21/0.57  fof(f234,plain,(
% 0.21/0.57    ( ! [X3] : (~r2_yellow_0(sK0,k1_tarski(sK5(sK0,X3,sK3))) | r1_lattice3(sK0,X3,sK3) | r1_lattice3(sK0,k1_tarski(sK5(sK0,X3,sK3)),sK6(sK0,k1_tarski(sK5(sK0,X3,sK3)),sK5(sK0,X3,sK3))) | sK5(sK0,X3,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,X3,sK3)))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f233,f89])).
% 0.21/0.57  fof(f233,plain,(
% 0.21/0.57    ( ! [X3] : (r1_lattice3(sK0,X3,sK3) | ~m1_subset_1(sK5(sK0,X3,sK3),u1_struct_0(sK0)) | ~r2_yellow_0(sK0,k1_tarski(sK5(sK0,X3,sK3))) | r1_lattice3(sK0,k1_tarski(sK5(sK0,X3,sK3)),sK6(sK0,k1_tarski(sK5(sK0,X3,sK3)),sK5(sK0,X3,sK3))) | sK5(sK0,X3,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,X3,sK3)))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f228,f75])).
% 0.21/0.57  fof(f228,plain,(
% 0.21/0.57    ( ! [X3] : (r1_lattice3(sK0,X3,sK3) | ~m1_subset_1(sK5(sK0,X3,sK3),u1_struct_0(sK0)) | ~r2_yellow_0(sK0,k1_tarski(sK5(sK0,X3,sK3))) | ~l1_orders_2(sK0) | r1_lattice3(sK0,k1_tarski(sK5(sK0,X3,sK3)),sK6(sK0,k1_tarski(sK5(sK0,X3,sK3)),sK5(sK0,X3,sK3))) | sK5(sK0,X3,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,X3,sK3)))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(resolution,[],[f213,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,sK6(X0,X1,X2)) | k2_yellow_0(X0,X1) = X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f933,plain,(
% 0.21/0.57    ~spl7_3 | ~spl7_4 | spl7_9 | ~spl7_69),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f932])).
% 0.21/0.57  fof(f932,plain,(
% 0.21/0.57    $false | (~spl7_3 | ~spl7_4 | spl7_9 | ~spl7_69)),
% 0.21/0.57    inference(subsumption_resolution,[],[f931,f131])).
% 0.21/0.57  fof(f931,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK1,sK3) | (~spl7_3 | ~spl7_4 | ~spl7_69)),
% 0.21/0.57    inference(subsumption_resolution,[],[f930,f75])).
% 0.21/0.57  fof(f930,plain,(
% 0.21/0.57    ~l1_orders_2(sK0) | r1_lattice3(sK0,sK1,sK3) | (~spl7_4 | ~spl7_69)),
% 0.21/0.57    inference(subsumption_resolution,[],[f927,f79])).
% 0.21/0.57  fof(f927,plain,(
% 0.21/0.57    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,sK1,sK3) | ~spl7_69),
% 0.21/0.57    inference(resolution,[],[f924,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK5(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r1_lattice3(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f924,plain,(
% 0.21/0.57    r1_orders_2(sK0,sK3,sK5(sK0,sK1,sK3)) | ~spl7_69),
% 0.21/0.57    inference(avatar_component_clause,[],[f923])).
% 0.21/0.57  fof(f893,plain,(
% 0.21/0.57    ~spl7_3 | ~spl7_4 | spl7_9 | spl7_68),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f892])).
% 0.21/0.57  fof(f892,plain,(
% 0.21/0.57    $false | (~spl7_3 | ~spl7_4 | spl7_9 | spl7_68)),
% 0.21/0.57    inference(subsumption_resolution,[],[f891,f131])).
% 0.21/0.57  fof(f891,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK1,sK3) | (~spl7_3 | ~spl7_4 | spl7_68)),
% 0.21/0.57    inference(resolution,[],[f872,f89])).
% 0.21/0.57  fof(f872,plain,(
% 0.21/0.57    ~m1_subset_1(sK5(sK0,sK1,sK3),u1_struct_0(sK0)) | spl7_68),
% 0.21/0.57    inference(avatar_component_clause,[],[f871])).
% 0.21/0.57  fof(f845,plain,(
% 0.21/0.57    spl7_65 | ~spl7_24 | ~spl7_60),
% 0.21/0.57    inference(avatar_split_clause,[],[f788,f780,f307,f843])).
% 0.21/0.57  fof(f307,plain,(
% 0.21/0.57    spl7_24 <=> r1_tarski(k1_tarski(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.57  fof(f788,plain,(
% 0.21/0.57    r1_tarski(k1_tarski(sK5(sK0,sK1,sK3)),sK2) | (~spl7_24 | ~spl7_60)),
% 0.21/0.57    inference(superposition,[],[f308,f781])).
% 0.21/0.57  fof(f781,plain,(
% 0.21/0.57    sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | ~spl7_60),
% 0.21/0.57    inference(avatar_component_clause,[],[f780])).
% 0.21/0.57  fof(f308,plain,(
% 0.21/0.57    r1_tarski(k1_tarski(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),sK2) | ~spl7_24),
% 0.21/0.57    inference(avatar_component_clause,[],[f307])).
% 0.21/0.57  fof(f785,plain,(
% 0.21/0.57    spl7_60 | spl7_61 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_9 | ~spl7_19),
% 0.21/0.57    inference(avatar_split_clause,[],[f623,f215,f118,f78,f74,f70,f66,f783,f780])).
% 0.21/0.57  fof(f623,plain,(
% 0.21/0.57    m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),u1_struct_0(sK0)) | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | spl7_9 | ~spl7_19)),
% 0.21/0.57    inference(subsumption_resolution,[],[f622,f131])).
% 0.21/0.57  fof(f622,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK1,sK3) | m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,sK1,sK3)),sK5(sK0,sK1,sK3)),u1_struct_0(sK0)) | sK5(sK0,sK1,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_19)),
% 0.21/0.57    inference(resolution,[],[f232,f216])).
% 0.21/0.57  fof(f232,plain,(
% 0.21/0.57    ( ! [X2] : (~r2_yellow_0(sK0,k1_tarski(sK5(sK0,X2,sK3))) | r1_lattice3(sK0,X2,sK3) | m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,X2,sK3)),sK5(sK0,X2,sK3)),u1_struct_0(sK0)) | sK5(sK0,X2,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,X2,sK3)))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f231,f89])).
% 0.21/0.57  fof(f231,plain,(
% 0.21/0.57    ( ! [X2] : (r1_lattice3(sK0,X2,sK3) | ~m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0)) | ~r2_yellow_0(sK0,k1_tarski(sK5(sK0,X2,sK3))) | m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,X2,sK3)),sK5(sK0,X2,sK3)),u1_struct_0(sK0)) | sK5(sK0,X2,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,X2,sK3)))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f227,f75])).
% 0.21/0.57  fof(f227,plain,(
% 0.21/0.57    ( ! [X2] : (r1_lattice3(sK0,X2,sK3) | ~m1_subset_1(sK5(sK0,X2,sK3),u1_struct_0(sK0)) | ~r2_yellow_0(sK0,k1_tarski(sK5(sK0,X2,sK3))) | ~l1_orders_2(sK0) | m1_subset_1(sK6(sK0,k1_tarski(sK5(sK0,X2,sK3)),sK5(sK0,X2,sK3)),u1_struct_0(sK0)) | sK5(sK0,X2,sK3) = k2_yellow_0(sK0,k1_tarski(sK5(sK0,X2,sK3)))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(resolution,[],[f213,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~l1_orders_2(X0) | m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) | k2_yellow_0(X0,X1) = X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f572,plain,(
% 0.21/0.57    ~spl7_9 | ~spl7_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f124,f121,f118])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    ~r1_lattice3(sK0,sK1,sK3) | ~spl7_10),
% 0.21/0.57    inference(subsumption_resolution,[],[f33,f122])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ~r1_lattice3(sK0,sK2,sK3) | ~r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & ! [X3] : (r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3)) & ! [X4] : (? [X5] : (k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5) & m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : (r2_yellow_0(X0,X6) | k1_xboole_0 = X6 | ~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ? [X0] : (? [X1] : (? [X2] : ((? [X7] : ((r1_lattice3(X0,X1,X7) <~> r1_lattice3(X0,X2,X7)) & m1_subset_1(X7,u1_struct_0(X0))) & (! [X3] : ((r2_hidden(k2_yellow_0(X0,X3),X2) | k1_xboole_0 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(X1)) | ~v1_finset_1(X3))) & ! [X4] : ((? [X5] : ((k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5)) & (m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5))) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & ! [X6] : ((r2_yellow_0(X0,X6) | k1_xboole_0 = X6) | (~m1_subset_1(X6,k1_zfmisc_1(X1)) | ~v1_finset_1(X6))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ~! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 0.21/0.57    inference(pure_predicate_removal,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(X1)) & v1_finset_1(X5)) => ~(k2_yellow_0(X0,X5) = X4 & r2_yellow_0(X0,X5))) & r2_hidden(X4,X2))) & ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(X1)) & v1_finset_1(X6)) => (k1_xboole_0 != X6 => r2_yellow_0(X0,X6)))) => ! [X7] : (m1_subset_1(X7,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X7) <=> r1_lattice3(X0,X2,X7)))))))),
% 0.21/0.57    inference(rectify,[],[f12])).
% 0.21/0.57  fof(f12,negated_conjecture,(
% 0.21/0.57    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 0.21/0.57    inference(negated_conjecture,[],[f11])).
% 0.21/0.57  fof(f11,conjecture,(
% 0.21/0.57    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_hidden(k2_yellow_0(X0,X3),X2))) & ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(X1)) & v1_finset_1(X4)) => ~(k2_yellow_0(X0,X4) = X3 & r2_yellow_0(X0,X4))) & r2_hidden(X3,X2))) & ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X1)) & v1_finset_1(X3)) => (k1_xboole_0 != X3 => r2_yellow_0(X0,X3)))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X3) <=> r1_lattice3(X0,X2,X3)))))))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_waybel_0)).
% 0.21/0.57  fof(f559,plain,(
% 0.21/0.57    ~spl7_3 | ~spl7_4 | spl7_10 | ~spl7_44),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f558])).
% 0.21/0.57  fof(f558,plain,(
% 0.21/0.57    $false | (~spl7_3 | ~spl7_4 | spl7_10 | ~spl7_44)),
% 0.21/0.57    inference(subsumption_resolution,[],[f557,f290])).
% 0.21/0.57  fof(f290,plain,(
% 0.21/0.57    ~r1_lattice3(sK0,sK2,sK3) | spl7_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f121])).
% 0.21/0.57  fof(f557,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK2,sK3) | (~spl7_3 | ~spl7_4 | ~spl7_44)),
% 0.21/0.57    inference(subsumption_resolution,[],[f556,f75])).
% 0.21/0.57  fof(f556,plain,(
% 0.21/0.57    ~l1_orders_2(sK0) | r1_lattice3(sK0,sK2,sK3) | (~spl7_4 | ~spl7_44)),
% 0.21/0.57    inference(subsumption_resolution,[],[f553,f79])).
% 0.21/0.57  fof(f553,plain,(
% 0.21/0.57    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,sK2,sK3) | ~spl7_44),
% 0.21/0.57    inference(resolution,[],[f541,f45])).
% 0.21/0.57  fof(f541,plain,(
% 0.21/0.57    r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3)) | ~spl7_44),
% 0.21/0.57    inference(avatar_component_clause,[],[f540])).
% 0.21/0.57  fof(f540,plain,(
% 0.21/0.57    spl7_44 <=> r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.21/0.57  fof(f542,plain,(
% 0.21/0.57    spl7_44 | ~spl7_4 | ~spl7_42 | ~spl7_43),
% 0.21/0.57    inference(avatar_split_clause,[],[f515,f501,f493,f78,f540])).
% 0.21/0.57  fof(f493,plain,(
% 0.21/0.57    spl7_42 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_orders_2(sK0,X0,sK5(sK0,sK2,sK3)) | ~r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 0.21/0.57  fof(f501,plain,(
% 0.21/0.57    spl7_43 <=> r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.21/0.57  fof(f515,plain,(
% 0.21/0.57    r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3)) | (~spl7_4 | ~spl7_42 | ~spl7_43)),
% 0.21/0.57    inference(subsumption_resolution,[],[f509,f79])).
% 0.21/0.57  fof(f509,plain,(
% 0.21/0.57    r1_orders_2(sK0,sK3,sK5(sK0,sK2,sK3)) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | (~spl7_42 | ~spl7_43)),
% 0.21/0.57    inference(resolution,[],[f502,f494])).
% 0.21/0.57  fof(f494,plain,(
% 0.21/0.57    ( ! [X0] : (~r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X0) | r1_orders_2(sK0,X0,sK5(sK0,sK2,sK3)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_42),
% 0.21/0.57    inference(avatar_component_clause,[],[f493])).
% 0.21/0.57  fof(f502,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) | ~spl7_43),
% 0.21/0.57    inference(avatar_component_clause,[],[f501])).
% 0.21/0.57  fof(f503,plain,(
% 0.21/0.57    spl7_43 | ~spl7_3 | ~spl7_4 | ~spl7_9 | ~spl7_34),
% 0.21/0.57    inference(avatar_split_clause,[],[f498,f417,f118,f78,f74,f501])).
% 0.21/0.57  fof(f417,plain,(
% 0.21/0.57    spl7_34 <=> r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.21/0.57  fof(f498,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) | (~spl7_3 | ~spl7_4 | ~spl7_9 | ~spl7_34)),
% 0.21/0.57    inference(subsumption_resolution,[],[f497,f75])).
% 0.21/0.57  fof(f497,plain,(
% 0.21/0.57    ~l1_orders_2(sK0) | r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) | (~spl7_4 | ~spl7_9 | ~spl7_34)),
% 0.21/0.57    inference(subsumption_resolution,[],[f496,f79])).
% 0.21/0.57  fof(f496,plain,(
% 0.21/0.57    ~m1_subset_1(sK3,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),sK3) | (~spl7_9 | ~spl7_34)),
% 0.21/0.57    inference(resolution,[],[f425,f119])).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK1,sK3) | ~spl7_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f118])).
% 0.21/0.57  fof(f425,plain,(
% 0.21/0.57    ( ! [X2,X3] : (~r1_lattice3(X2,sK1,X3) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l1_orders_2(X2) | r1_lattice3(X2,sK4(sK5(sK0,sK2,sK3)),X3)) ) | ~spl7_34),
% 0.21/0.57    inference(resolution,[],[f418,f62])).
% 0.21/0.57  fof(f418,plain,(
% 0.21/0.57    r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1) | ~spl7_34),
% 0.21/0.57    inference(avatar_component_clause,[],[f417])).
% 0.21/0.57  fof(f495,plain,(
% 0.21/0.57    spl7_42 | ~spl7_39 | ~spl7_3 | ~spl7_28 | ~spl7_35),
% 0.21/0.57    inference(avatar_split_clause,[],[f429,f421,f331,f74,f451,f493])).
% 0.21/0.57  fof(f451,plain,(
% 0.21/0.57    spl7_39 <=> m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.21/0.57  fof(f331,plain,(
% 0.21/0.57    spl7_28 <=> r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.57  fof(f421,plain,(
% 0.21/0.57    spl7_35 <=> sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.57  fof(f429,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X0) | r1_orders_2(sK0,X0,sK5(sK0,sK2,sK3))) ) | (~spl7_3 | ~spl7_28 | ~spl7_35)),
% 0.21/0.57    inference(subsumption_resolution,[],[f428,f332])).
% 0.21/0.57  fof(f332,plain,(
% 0.21/0.57    r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~spl7_28),
% 0.21/0.57    inference(avatar_component_clause,[],[f331])).
% 0.21/0.57  fof(f428,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | ~r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X0) | r1_orders_2(sK0,X0,sK5(sK0,sK2,sK3))) ) | (~spl7_3 | ~spl7_35)),
% 0.21/0.57    inference(subsumption_resolution,[],[f426,f75])).
% 0.21/0.57  fof(f426,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r1_lattice3(sK0,sK4(sK5(sK0,sK2,sK3)),X0) | r1_orders_2(sK0,X0,sK5(sK0,sK2,sK3))) ) | ~spl7_35),
% 0.21/0.57    inference(superposition,[],[f64,f422])).
% 0.21/0.57  fof(f422,plain,(
% 0.21/0.57    sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | ~spl7_35),
% 0.21/0.57    inference(avatar_component_clause,[],[f421])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (~m1_subset_1(k2_yellow_0(X0,X1),u1_struct_0(X0)) | ~l1_orders_2(X0) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X3) | r1_orders_2(X0,X3,k2_yellow_0(X0,X1))) )),
% 0.21/0.57    inference(equality_resolution,[],[f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_yellow_0(X0,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r1_lattice3(X0,X1,X3) | r1_orders_2(X0,X3,X2) | k2_yellow_0(X0,X1) != X2) )),
% 0.21/0.57    inference(cnf_transformation,[],[f21])).
% 0.21/0.57  fof(f456,plain,(
% 0.21/0.57    ~spl7_3 | ~spl7_4 | spl7_10 | spl7_39),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f455])).
% 0.21/0.57  fof(f455,plain,(
% 0.21/0.57    $false | (~spl7_3 | ~spl7_4 | spl7_10 | spl7_39)),
% 0.21/0.57    inference(subsumption_resolution,[],[f454,f290])).
% 0.21/0.57  fof(f454,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK2,sK3) | (~spl7_3 | ~spl7_4 | spl7_39)),
% 0.21/0.57    inference(resolution,[],[f452,f89])).
% 0.21/0.57  fof(f452,plain,(
% 0.21/0.57    ~m1_subset_1(sK5(sK0,sK2,sK3),u1_struct_0(sK0)) | spl7_39),
% 0.21/0.57    inference(avatar_component_clause,[],[f451])).
% 0.21/0.57  fof(f423,plain,(
% 0.21/0.57    spl7_35 | ~spl7_3 | ~spl7_4 | spl7_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f402,f121,f78,f74,f421])).
% 0.21/0.57  fof(f402,plain,(
% 0.21/0.57    sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | (~spl7_3 | ~spl7_4 | spl7_10)),
% 0.21/0.57    inference(subsumption_resolution,[],[f302,f290])).
% 0.21/0.57  fof(f302,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK2,sK3) | sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f301])).
% 0.21/0.57  fof(f301,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK2,sK3) | sK5(sK0,sK2,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | r1_lattice3(sK0,sK2,sK3) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(resolution,[],[f171,f90])).
% 0.21/0.57  fof(f90,plain,(
% 0.21/0.57    ( ! [X3] : (r2_hidden(sK5(sK0,X3,sK3),X3) | r1_lattice3(sK0,X3,sK3)) ) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(subsumption_resolution,[],[f84,f75])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    ( ! [X3] : (~l1_orders_2(sK0) | r2_hidden(sK5(sK0,X3,sK3),X3) | r1_lattice3(sK0,X3,sK3)) ) | ~spl7_4),
% 0.21/0.57    inference(resolution,[],[f79,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | r2_hidden(sK5(X0,X1,X2),X1) | r1_lattice3(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f171,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(sK5(sK0,X0,sK3),sK2) | r1_lattice3(sK0,X0,sK3) | sK5(sK0,X0,sK3) = k2_yellow_0(sK0,sK4(sK5(sK0,X0,sK3)))) ) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(resolution,[],[f89,f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | k2_yellow_0(sK0,sK4(X4)) = X4) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f419,plain,(
% 0.21/0.57    spl7_34 | ~spl7_33),
% 0.21/0.57    inference(avatar_split_clause,[],[f413,f408,f417])).
% 0.21/0.57  fof(f408,plain,(
% 0.21/0.57    spl7_33 <=> m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_33])])).
% 0.21/0.57  fof(f413,plain,(
% 0.21/0.57    r1_tarski(sK4(sK5(sK0,sK2,sK3)),sK1) | ~spl7_33),
% 0.21/0.57    inference(resolution,[],[f409,f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.21/0.57    inference(unused_predicate_definition_removal,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.57  fof(f409,plain,(
% 0.21/0.57    m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | ~spl7_33),
% 0.21/0.57    inference(avatar_component_clause,[],[f408])).
% 0.21/0.57  fof(f410,plain,(
% 0.21/0.57    spl7_33 | ~spl7_3 | ~spl7_4 | spl7_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f401,f121,f78,f74,f408])).
% 0.21/0.57  fof(f401,plain,(
% 0.21/0.57    m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | (~spl7_3 | ~spl7_4 | spl7_10)),
% 0.21/0.57    inference(subsumption_resolution,[],[f242,f290])).
% 0.21/0.57  fof(f242,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK2,sK3) | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f241])).
% 0.21/0.57  fof(f241,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK2,sK3) | m1_subset_1(sK4(sK5(sK0,sK2,sK3)),k1_zfmisc_1(sK1)) | r1_lattice3(sK0,sK2,sK3) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(resolution,[],[f172,f90])).
% 0.21/0.57  fof(f172,plain,(
% 0.21/0.57    ( ! [X1] : (~r2_hidden(sK5(sK0,X1,sK3),sK2) | r1_lattice3(sK0,X1,sK3) | m1_subset_1(sK4(sK5(sK0,X1,sK3)),k1_zfmisc_1(sK1))) ) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(resolution,[],[f89,f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | m1_subset_1(sK4(X4),k1_zfmisc_1(sK1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f333,plain,(
% 0.21/0.57    spl7_28 | ~spl7_3 | ~spl7_4 | spl7_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f310,f121,f78,f74,f331])).
% 0.21/0.57  fof(f310,plain,(
% 0.21/0.57    r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | (~spl7_3 | ~spl7_4 | spl7_10)),
% 0.21/0.57    inference(subsumption_resolution,[],[f236,f290])).
% 0.21/0.57  fof(f236,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK2,sK3) | r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f235])).
% 0.21/0.57  fof(f235,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK2,sK3) | r2_yellow_0(sK0,sK4(sK5(sK0,sK2,sK3))) | r1_lattice3(sK0,sK2,sK3) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(resolution,[],[f173,f90])).
% 0.21/0.57  fof(f173,plain,(
% 0.21/0.57    ( ! [X2] : (~r2_hidden(sK5(sK0,X2,sK3),sK2) | r1_lattice3(sK0,X2,sK3) | r2_yellow_0(sK0,sK4(sK5(sK0,X2,sK3)))) ) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(resolution,[],[f89,f30])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | r2_yellow_0(sK0,sK4(X4))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f309,plain,(
% 0.21/0.57    spl7_24 | ~spl7_22),
% 0.21/0.57    inference(avatar_split_clause,[],[f303,f275,f307])).
% 0.21/0.57  fof(f275,plain,(
% 0.21/0.57    spl7_22 <=> m1_subset_1(k1_tarski(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),k1_zfmisc_1(sK2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.57  fof(f303,plain,(
% 0.21/0.57    r1_tarski(k1_tarski(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),sK2) | ~spl7_22),
% 0.21/0.57    inference(resolution,[],[f276,f54])).
% 0.21/0.57  fof(f276,plain,(
% 0.21/0.57    m1_subset_1(k1_tarski(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),k1_zfmisc_1(sK2)) | ~spl7_22),
% 0.21/0.57    inference(avatar_component_clause,[],[f275])).
% 0.21/0.57  fof(f277,plain,(
% 0.21/0.57    spl7_22 | ~spl7_21),
% 0.21/0.57    inference(avatar_split_clause,[],[f259,f238,f275])).
% 0.21/0.57  fof(f238,plain,(
% 0.21/0.57    spl7_21 <=> r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.57  fof(f259,plain,(
% 0.21/0.57    m1_subset_1(k1_tarski(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3)))),k1_zfmisc_1(sK2)) | ~spl7_21),
% 0.21/0.57    inference(resolution,[],[f239,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.21/0.57  fof(f239,plain,(
% 0.21/0.57    r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) | ~spl7_21),
% 0.21/0.57    inference(avatar_component_clause,[],[f238])).
% 0.21/0.57  fof(f257,plain,(
% 0.21/0.57    ~spl7_20),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f256])).
% 0.21/0.57  fof(f256,plain,(
% 0.21/0.57    $false | ~spl7_20),
% 0.21/0.57    inference(subsumption_resolution,[],[f248,f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    inference(cnf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    v1_xboole_0(k1_xboole_0)),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.57  fof(f248,plain,(
% 0.21/0.57    ~v1_xboole_0(k1_xboole_0) | ~spl7_20),
% 0.21/0.57    inference(superposition,[],[f60,f219])).
% 0.21/0.57  fof(f219,plain,(
% 0.21/0.57    k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | ~spl7_20),
% 0.21/0.57    inference(avatar_component_clause,[],[f218])).
% 0.21/0.57  fof(f218,plain,(
% 0.21/0.57    spl7_20 <=> k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.21/0.57  fof(f240,plain,(
% 0.21/0.57    spl7_21 | spl7_20 | ~spl7_3 | ~spl7_4 | spl7_9),
% 0.21/0.57    inference(avatar_split_clause,[],[f189,f118,f78,f74,f218,f238])).
% 0.21/0.57  fof(f189,plain,(
% 0.21/0.57    k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) | (~spl7_3 | ~spl7_4 | spl7_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f188,f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ( ! [X0] : (v1_finset_1(k1_tarski(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : v1_finset_1(k1_tarski(X0))),
% 0.21/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_finset_1)).
% 0.21/0.57  fof(f188,plain,(
% 0.21/0.57    ~v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) | (~spl7_3 | ~spl7_4 | spl7_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f186,f131])).
% 0.21/0.57  fof(f186,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK1,sK3) | ~v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_hidden(k2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))),sK2) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(resolution,[],[f162,f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(sK1)) | ~v1_finset_1(X3) | k1_xboole_0 = X3 | r2_hidden(k2_yellow_0(sK0,X3),sK2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f162,plain,(
% 0.21/0.57    ( ! [X0] : (m1_subset_1(k1_tarski(sK5(sK0,X0,sK3)),k1_zfmisc_1(X0)) | r1_lattice3(sK0,X0,sK3)) ) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(resolution,[],[f90,f51])).
% 0.21/0.57  fof(f220,plain,(
% 0.21/0.57    spl7_19 | spl7_20 | ~spl7_3 | ~spl7_4 | spl7_9),
% 0.21/0.57    inference(avatar_split_clause,[],[f191,f118,f78,f74,f218,f215])).
% 0.21/0.57  fof(f191,plain,(
% 0.21/0.57    k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (~spl7_3 | ~spl7_4 | spl7_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f190,f53])).
% 0.21/0.57  fof(f190,plain,(
% 0.21/0.57    ~v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (~spl7_3 | ~spl7_4 | spl7_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f187,f131])).
% 0.21/0.57  fof(f187,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK1,sK3) | ~v1_finset_1(k1_tarski(sK5(sK0,sK1,sK3))) | k1_xboole_0 = k1_tarski(sK5(sK0,sK1,sK3)) | r2_yellow_0(sK0,k1_tarski(sK5(sK0,sK1,sK3))) | (~spl7_3 | ~spl7_4)),
% 0.21/0.57    inference(resolution,[],[f162,f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(sK1)) | ~v1_finset_1(X6) | k1_xboole_0 = X6 | r2_yellow_0(sK0,X6)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f123,plain,(
% 0.21/0.57    spl7_9 | spl7_10),
% 0.21/0.57    inference(avatar_split_clause,[],[f32,f121,f118])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    r1_lattice3(sK0,sK2,sK3) | r1_lattice3(sK0,sK1,sK3)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    spl7_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f34,f78])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    m1_subset_1(sK3,u1_struct_0(sK0))),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    spl7_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f41,f74])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    l1_orders_2(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    spl7_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f40,f70])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    v3_orders_2(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ~spl7_1),
% 0.21/0.57    inference(avatar_split_clause,[],[f39,f66])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ~v2_struct_0(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f17])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (20011)------------------------------
% 0.21/0.57  % (20011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20011)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (20011)Memory used [KB]: 7419
% 0.21/0.57  % (20011)Time elapsed: 0.144 s
% 0.21/0.57  % (20011)------------------------------
% 0.21/0.57  % (20011)------------------------------
% 0.21/0.57  % (20009)Success in time 0.207 s
%------------------------------------------------------------------------------
