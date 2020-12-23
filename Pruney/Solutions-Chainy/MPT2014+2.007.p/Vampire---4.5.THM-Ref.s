%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 201 expanded)
%              Number of leaves         :   26 (  92 expanded)
%              Depth                    :    7
%              Number of atoms          :  389 ( 724 expanded)
%              Number of equality atoms :   20 (  33 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f372,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f91,f97,f109,f116,f122,f127,f133,f138,f174,f208,f302,f336,f371])).

fof(f371,plain,
    ( spl7_5
    | ~ spl7_49 ),
    inference(avatar_split_clause,[],[f370,f333,f77])).

fof(f77,plain,
    ( spl7_5
  <=> r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f333,plain,
    ( spl7_49
  <=> r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f370,plain,
    ( r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl7_49 ),
    inference(resolution,[],[f335,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f335,plain,
    ( r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f333])).

fof(f336,plain,
    ( spl7_5
    | spl7_49
    | ~ spl7_27
    | ~ spl7_44 ),
    inference(avatar_split_clause,[],[f309,f299,f206,f333,f77])).

fof(f206,plain,
    ( spl7_27
  <=> ! [X2] :
        ( r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X2)
        | r2_hidden(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X2)),u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f299,plain,
    ( spl7_44
  <=> sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) = sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f309,plain,
    ( r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)),u1_struct_0(sK1))
    | r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | ~ spl7_27
    | ~ spl7_44 ),
    inference(superposition,[],[f207,f301])).

fof(f301,plain,
    ( sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) = sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f299])).

fof(f207,plain,
    ( ! [X2] :
        ( r2_hidden(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X2)),u1_struct_0(sK1))
        | r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X2) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f206])).

fof(f302,plain,
    ( spl7_44
    | spl7_5
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f297,f136,f77,f299])).

fof(f136,plain,
    ( spl7_15
  <=> ! [X0] :
        ( sK5(sK1,sK2,X0) = X0
        | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f297,plain,
    ( sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) = sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)))
    | spl7_5
    | ~ spl7_15 ),
    inference(resolution,[],[f175,f79])).

fof(f79,plain,
    ( ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))
    | spl7_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f175,plain,
    ( ! [X0] :
        ( r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X0)
        | sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X0) = sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X0)) )
    | ~ spl7_15 ),
    inference(resolution,[],[f137,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | sK5(sK1,sK2,X0) = X0 )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f136])).

fof(f208,plain,
    ( spl7_10
    | spl7_27
    | ~ spl7_22 ),
    inference(avatar_split_clause,[],[f204,f172,f206,f104])).

fof(f104,plain,
    ( spl7_10
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f172,plain,
    ( spl7_22
  <=> ! [X0] :
        ( m1_subset_1(sK5(sK1,sK2,X0),u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f204,plain,
    ( ! [X2] :
        ( r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X2)
        | v1_xboole_0(u1_struct_0(sK1))
        | r2_hidden(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X2)),u1_struct_0(sK1)) )
    | ~ spl7_22 ),
    inference(resolution,[],[f188,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f188,plain,
    ( ! [X0] :
        ( m1_subset_1(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X0)),u1_struct_0(sK1))
        | r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X0) )
    | ~ spl7_22 ),
    inference(resolution,[],[f173,f44])).

fof(f173,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))
        | m1_subset_1(sK5(sK1,sK2,X0),u1_struct_0(sK1)) )
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f172])).

fof(f174,plain,
    ( spl7_22
    | ~ spl7_14
    | spl7_2
    | ~ spl7_6
    | ~ spl7_3
    | spl7_4
    | ~ spl7_1
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f170,f119,f57,f72,f67,f82,f62,f130,f172])).

fof(f130,plain,
    ( spl7_14
  <=> l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f62,plain,
    ( spl7_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f82,plain,
    ( spl7_6
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f67,plain,
    ( spl7_3
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f72,plain,
    ( spl7_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f57,plain,
    ( spl7_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f119,plain,
    ( spl7_12
  <=> v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f170,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
        | m1_subset_1(sK5(sK1,sK2,X0),u1_struct_0(sK1))
        | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) )
    | ~ spl7_12 ),
    inference(resolution,[],[f55,f121])).

fof(f121,plain,
    ( v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | m1_subset_1(sK5(X1,X2,X4),u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | m1_subset_1(sK5(X1,X2,X4),u1_struct_0(X1))
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) )
                  | ~ l1_waybel_0(X3,X0)
                  | ~ v6_waybel_0(X3,X0) )
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => ! [X3] :
                  ( ( l1_waybel_0(X3,X0)
                    & v6_waybel_0(X3,X0) )
                 => ( k4_waybel_9(X0,X1,X2) = X3
                  <=> ( u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3))
                      & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3)))
                      & ! [X4] :
                          ( r2_hidden(X4,u1_struct_0(X3))
                        <=> ? [X5] :
                              ( r1_orders_2(X1,X2,X5)
                              & X4 = X5
                              & m1_subset_1(X5,u1_struct_0(X1)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).

fof(f138,plain,
    ( spl7_15
    | ~ spl7_14
    | spl7_2
    | ~ spl7_6
    | ~ spl7_3
    | spl7_4
    | ~ spl7_1
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f134,f119,f57,f72,f67,f82,f62,f130,f136])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | ~ l1_waybel_0(sK1,sK0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | v2_struct_0(sK0)
        | ~ l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
        | sK5(sK1,sK2,X0) = X0
        | ~ r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) )
    | ~ spl7_12 ),
    inference(resolution,[],[f54,f121])).

fof(f54,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X0)
      | ~ l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
      | sK5(X1,X2,X4) = X4
      | ~ r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2))) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_waybel_0(X3,X0)
      | ~ l1_waybel_0(X3,X0)
      | sK5(X1,X2,X4) = X4
      | ~ r2_hidden(X4,u1_struct_0(X3))
      | k4_waybel_9(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f133,plain,
    ( spl7_14
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(avatar_split_clause,[],[f128,f125,f82,f130])).

fof(f125,plain,
    ( spl7_13
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f128,plain,
    ( l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ spl7_6
    | ~ spl7_13 ),
    inference(resolution,[],[f126,f84])).

fof(f84,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f126,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) )
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f127,plain,
    ( spl7_13
    | spl7_2
    | spl7_4
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f123,f67,f57,f72,f62,f125])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f47,f69])).

fof(f69,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l1_waybel_0(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)
        & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).

fof(f122,plain,
    ( spl7_12
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(avatar_split_clause,[],[f117,f114,f82,f119])).

fof(f114,plain,
    ( spl7_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v6_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f117,plain,
    ( v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)
    | ~ spl7_6
    | ~ spl7_11 ),
    inference(resolution,[],[f115,f84])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v6_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl7_11
    | spl7_2
    | spl7_4
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f112,f67,f57,f72,f62,f114])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | v6_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f46,f69])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f109,plain,
    ( spl7_4
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f108,f104,f94,f72])).

fof(f94,plain,
    ( spl7_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f108,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_10 ),
    inference(resolution,[],[f106,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f106,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f97,plain,
    ( spl7_8
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f92,f88,f94])).

fof(f88,plain,
    ( spl7_7
  <=> l1_orders_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f92,plain,
    ( l1_struct_0(sK1)
    | ~ spl7_7 ),
    inference(resolution,[],[f90,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

% (6649)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f90,plain,
    ( l1_orders_2(sK1)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f91,plain,
    ( spl7_7
    | ~ spl7_1
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f86,f67,f57,f88])).

fof(f86,plain,
    ( ~ l1_struct_0(sK0)
    | l1_orders_2(sK1)
    | ~ spl7_3 ),
    inference(resolution,[],[f31,f69])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_waybel_0(X1,X0)
      | ~ l1_struct_0(X0)
      | l1_orders_2(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_orders_2(X1)
          | ~ l1_waybel_0(X1,X0) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_waybel_0(X1,X0)
         => l1_orders_2(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).

fof(f85,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f24,f82])).

fof(f24,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1))
              & m1_subset_1(X2,u1_struct_0(X1)) )
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X1))
               => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).

fof(f80,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f25,f77])).

fof(f25,plain,(
    ~ r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f75,plain,(
    ~ spl7_4 ),
    inference(avatar_split_clause,[],[f26,f72])).

fof(f26,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f70,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f60,plain,(
    spl7_1 ),
    inference(avatar_split_clause,[],[f29,f57])).

fof(f29,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:26:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (6644)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.52  % (6635)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (6627)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.52  % (6625)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (6635)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (6634)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (6624)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (6631)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (6626)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (6619)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (6621)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (6621)Refutation not found, incomplete strategy% (6621)------------------------------
% 0.21/0.53  % (6621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6618)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (6621)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6621)Memory used [KB]: 10746
% 0.21/0.53  % (6621)Time elapsed: 0.112 s
% 0.21/0.53  % (6621)------------------------------
% 0.21/0.53  % (6621)------------------------------
% 0.21/0.53  % (6618)Refutation not found, incomplete strategy% (6618)------------------------------
% 0.21/0.53  % (6618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (6618)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (6618)Memory used [KB]: 1663
% 0.21/0.53  % (6618)Time elapsed: 0.123 s
% 0.21/0.53  % (6618)------------------------------
% 0.21/0.53  % (6618)------------------------------
% 0.21/0.54  % (6629)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (6646)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (6622)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f372,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f91,f97,f109,f116,f122,f127,f133,f138,f174,f208,f302,f336,f371])).
% 0.21/0.54  fof(f371,plain,(
% 0.21/0.54    spl7_5 | ~spl7_49),
% 0.21/0.54    inference(avatar_split_clause,[],[f370,f333,f77])).
% 0.21/0.54  fof(f77,plain,(
% 0.21/0.54    spl7_5 <=> r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.54  fof(f333,plain,(
% 0.21/0.54    spl7_49 <=> r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)),u1_struct_0(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 0.21/0.54  fof(f370,plain,(
% 0.21/0.54    r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) | ~spl7_49),
% 0.21/0.54    inference(resolution,[],[f335,f45])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.54  fof(f335,plain,(
% 0.21/0.54    r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)),u1_struct_0(sK1)) | ~spl7_49),
% 0.21/0.54    inference(avatar_component_clause,[],[f333])).
% 0.21/0.54  fof(f336,plain,(
% 0.21/0.54    spl7_5 | spl7_49 | ~spl7_27 | ~spl7_44),
% 0.21/0.54    inference(avatar_split_clause,[],[f309,f299,f206,f333,f77])).
% 0.21/0.54  fof(f206,plain,(
% 0.21/0.54    spl7_27 <=> ! [X2] : (r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X2) | r2_hidden(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X2)),u1_struct_0(sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.54  fof(f299,plain,(
% 0.21/0.54    spl7_44 <=> sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) = sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 0.21/0.54  fof(f309,plain,(
% 0.21/0.54    r2_hidden(sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)),u1_struct_0(sK1)) | r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) | (~spl7_27 | ~spl7_44)),
% 0.21/0.54    inference(superposition,[],[f207,f301])).
% 0.21/0.54  fof(f301,plain,(
% 0.21/0.54    sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) = sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))) | ~spl7_44),
% 0.21/0.54    inference(avatar_component_clause,[],[f299])).
% 0.21/0.54  fof(f207,plain,(
% 0.21/0.54    ( ! [X2] : (r2_hidden(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X2)),u1_struct_0(sK1)) | r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X2)) ) | ~spl7_27),
% 0.21/0.54    inference(avatar_component_clause,[],[f206])).
% 0.21/0.54  fof(f302,plain,(
% 0.21/0.54    spl7_44 | spl7_5 | ~spl7_15),
% 0.21/0.54    inference(avatar_split_clause,[],[f297,f136,f77,f299])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl7_15 <=> ! [X0] : (sK5(sK1,sK2,X0) = X0 | ~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.54  fof(f297,plain,(
% 0.21/0.54    sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) = sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))) | (spl7_5 | ~spl7_15)),
% 0.21/0.54    inference(resolution,[],[f175,f79])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1)) | spl7_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f77])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ( ! [X0] : (r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X0) | sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X0) = sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X0))) ) | ~spl7_15),
% 0.21/0.54    inference(resolution,[],[f137,f44])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK6(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f21])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | sK5(sK1,sK2,X0) = X0) ) | ~spl7_15),
% 0.21/0.54    inference(avatar_component_clause,[],[f136])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    spl7_10 | spl7_27 | ~spl7_22),
% 0.21/0.54    inference(avatar_split_clause,[],[f204,f172,f206,f104])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    spl7_10 <=> v1_xboole_0(u1_struct_0(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.54  fof(f172,plain,(
% 0.21/0.54    spl7_22 <=> ! [X0] : (m1_subset_1(sK5(sK1,sK2,X0),u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.54  fof(f204,plain,(
% 0.21/0.54    ( ! [X2] : (r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X2) | v1_xboole_0(u1_struct_0(sK1)) | r2_hidden(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X2)),u1_struct_0(sK1))) ) | ~spl7_22),
% 0.21/0.54    inference(resolution,[],[f188,f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.54  fof(f188,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK5(sK1,sK2,sK6(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X0)),u1_struct_0(sK1)) | r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),X0)) ) | ~spl7_22),
% 0.21/0.54    inference(resolution,[],[f173,f44])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2))) | m1_subset_1(sK5(sK1,sK2,X0),u1_struct_0(sK1))) ) | ~spl7_22),
% 0.21/0.54    inference(avatar_component_clause,[],[f172])).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    spl7_22 | ~spl7_14 | spl7_2 | ~spl7_6 | ~spl7_3 | spl7_4 | ~spl7_1 | ~spl7_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f170,f119,f57,f72,f67,f82,f62,f130,f172])).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    spl7_14 <=> l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    spl7_2 <=> v2_struct_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    spl7_6 <=> m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl7_3 <=> l1_waybel_0(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    spl7_4 <=> v2_struct_0(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    spl7_1 <=> l1_struct_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    spl7_12 <=> v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.54  fof(f170,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | v2_struct_0(sK0) | ~l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) | m1_subset_1(sK5(sK1,sK2,X0),u1_struct_0(sK1)) | ~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) ) | ~spl7_12),
% 0.21/0.54    inference(resolution,[],[f55,f121])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) | ~spl7_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f119])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X0) | ~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | m1_subset_1(sK5(X1,X2,X4),u1_struct_0(X1)) | ~r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f33])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(X3,X0) | ~l1_waybel_0(X3,X0) | m1_subset_1(sK5(X1,X2,X4),u1_struct_0(X1)) | ~r2_hidden(X4,u1_struct_0(X3)) | k4_waybel_9(X0,X1,X2) != X3) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | ~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1)))))) | (~l1_waybel_0(X3,X0) | ~v6_waybel_0(X3,X0))) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => ! [X3] : ((l1_waybel_0(X3,X0) & v6_waybel_0(X3,X0)) => (k4_waybel_9(X0,X1,X2) = X3 <=> (u1_waybel_0(X0,X3) = k2_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_waybel_0(X0,X1),u1_struct_0(X3)) & r2_relset_1(u1_struct_0(X3),u1_struct_0(X3),u1_orders_2(X3),k1_toler_1(u1_orders_2(X1),u1_struct_0(X3))) & ! [X4] : (r2_hidden(X4,u1_struct_0(X3)) <=> ? [X5] : (r1_orders_2(X1,X2,X5) & X4 = X5 & m1_subset_1(X5,u1_struct_0(X1))))))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_waybel_9)).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    spl7_15 | ~spl7_14 | spl7_2 | ~spl7_6 | ~spl7_3 | spl7_4 | ~spl7_1 | ~spl7_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f134,f119,f57,f72,f67,f82,f62,f130,f136])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_struct_0(sK0) | v2_struct_0(sK1) | ~l1_waybel_0(sK1,sK0) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | v2_struct_0(sK0) | ~l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) | sK5(sK1,sK2,X0) = X0 | ~r2_hidden(X0,u1_struct_0(k4_waybel_9(sK0,sK1,sK2)))) ) | ~spl7_12),
% 0.21/0.54    inference(resolution,[],[f54,f121])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (~v6_waybel_0(k4_waybel_9(X0,X1,X2),X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X0) | ~l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) | sK5(X1,X2,X4) = X4 | ~r2_hidden(X4,u1_struct_0(k4_waybel_9(X0,X1,X2)))) )),
% 0.21/0.54    inference(equality_resolution,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_waybel_0(X3,X0) | ~l1_waybel_0(X3,X0) | sK5(X1,X2,X4) = X4 | ~r2_hidden(X4,u1_struct_0(X3)) | k4_waybel_9(X0,X1,X2) != X3) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    spl7_14 | ~spl7_6 | ~spl7_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f128,f125,f82,f130])).
% 0.21/0.54  fof(f125,plain,(
% 0.21/0.54    spl7_13 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    l1_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) | (~spl7_6 | ~spl7_13)),
% 0.21/0.54    inference(resolution,[],[f126,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    m1_subset_1(sK2,u1_struct_0(sK1)) | ~spl7_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f82])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0)) ) | ~spl7_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f125])).
% 0.21/0.54  fof(f127,plain,(
% 0.21/0.54    spl7_13 | spl7_2 | spl7_4 | ~spl7_1 | ~spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f123,f67,f57,f72,f62,f125])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | l1_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0)) ) | ~spl7_3),
% 0.21/0.54    inference(resolution,[],[f47,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    l1_waybel_0(sK1,sK0) | ~spl7_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f67])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | l1_waybel_0(k4_waybel_9(X0,X1,X2),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k4_waybel_9(X0,X1,X2),X0) & v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_waybel_9)).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    spl7_12 | ~spl7_6 | ~spl7_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f117,f114,f82,f119])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    spl7_11 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | v6_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    v6_waybel_0(k4_waybel_9(sK0,sK1,sK2),sK0) | (~spl7_6 | ~spl7_11)),
% 0.21/0.54    inference(resolution,[],[f115,f84])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | v6_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0)) ) | ~spl7_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f114])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl7_11 | spl7_2 | spl7_4 | ~spl7_1 | ~spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f112,f67,f57,f72,f62,f114])).
% 0.21/0.54  fof(f112,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_struct_0(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK1)) | v6_waybel_0(k4_waybel_9(sK0,sK1,X0),sK0)) ) | ~spl7_3),
% 0.21/0.54    inference(resolution,[],[f46,f69])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | v2_struct_0(X1) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | v6_waybel_0(k4_waybel_9(X0,X1,X2),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f23])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    spl7_4 | ~spl7_8 | ~spl7_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f108,f104,f94,f72])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl7_8 <=> l1_struct_0(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl7_10),
% 0.21/0.54    inference(resolution,[],[f106,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    v1_xboole_0(u1_struct_0(sK1)) | ~spl7_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f104])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    spl7_8 | ~spl7_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f92,f88,f94])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    spl7_7 <=> l1_orders_2(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    l1_struct_0(sK1) | ~spl7_7),
% 0.21/0.54    inference(resolution,[],[f90,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  % (6649)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    l1_orders_2(sK1) | ~spl7_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f88])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    spl7_7 | ~spl7_1 | ~spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f86,f67,f57,f88])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ~l1_struct_0(sK0) | l1_orders_2(sK1) | ~spl7_3),
% 0.21/0.54    inference(resolution,[],[f31,f69])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~l1_waybel_0(X1,X0) | ~l1_struct_0(X0) | l1_orders_2(X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (l1_orders_2(X1) | ~l1_waybel_0(X1,X0)) | ~l1_struct_0(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_waybel_0(X1,X0) => l1_orders_2(X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_waybel_0)).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    spl7_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f24,f82])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1))) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,negated_conjecture,(
% 0.21/0.54    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f8])).
% 0.21/0.54  fof(f8,conjecture,(
% 0.21/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => r1_tarski(u1_struct_0(k4_waybel_9(X0,X1,X2)),u1_struct_0(X1)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_waybel_9)).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ~spl7_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f25,f77])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ~r1_tarski(u1_struct_0(k4_waybel_9(sK0,sK1,sK2)),u1_struct_0(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ~spl7_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f26,f72])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ~v2_struct_0(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    spl7_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f27,f67])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    l1_waybel_0(sK1,sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ~spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f28,f62])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ~v2_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    spl7_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f29,f57])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    l1_struct_0(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (6635)------------------------------
% 0.21/0.54  % (6635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (6635)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (6635)Memory used [KB]: 11001
% 0.21/0.54  % (6635)Time elapsed: 0.108 s
% 0.21/0.54  % (6635)------------------------------
% 0.21/0.54  % (6635)------------------------------
% 0.21/0.54  % (6615)Success in time 0.182 s
%------------------------------------------------------------------------------
