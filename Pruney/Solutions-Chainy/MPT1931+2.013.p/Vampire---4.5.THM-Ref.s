%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 350 expanded)
%              Number of leaves         :   32 ( 130 expanded)
%              Depth                    :   16
%              Number of atoms          :  560 (1705 expanded)
%              Number of equality atoms :   42 ( 161 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f633,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f86,f90,f94,f98,f102,f135,f141,f187,f269,f280,f457,f462,f496,f527,f543,f574,f594,f632])).

% (28438)Refutation not found, incomplete strategy% (28438)------------------------------
% (28438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28438)Termination reason: Refutation not found, incomplete strategy

% (28438)Memory used [KB]: 10618
% (28438)Time elapsed: 0.113 s
% (28438)------------------------------
% (28438)------------------------------
fof(f632,plain,
    ( ~ spl7_6
    | ~ spl7_35 ),
    inference(avatar_split_clause,[],[f623,f572,f100])).

fof(f100,plain,
    ( spl7_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f572,plain,
    ( spl7_35
  <=> r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f623,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_35 ),
    inference(resolution,[],[f573,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f573,plain,
    ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0)
    | ~ spl7_35 ),
    inference(avatar_component_clause,[],[f572])).

fof(f594,plain,
    ( ~ spl7_6
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f582,f541,f100])).

fof(f541,plain,
    ( spl7_31
  <=> r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f582,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl7_31 ),
    inference(resolution,[],[f542,f59])).

fof(f542,plain,
    ( r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0)
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f541])).

fof(f574,plain,
    ( spl7_35
    | spl7_1
    | ~ spl7_8
    | ~ spl7_19
    | ~ spl7_30 ),
    inference(avatar_split_clause,[],[f550,f537,f460,f139,f80,f572])).

fof(f80,plain,
    ( spl7_1
  <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f139,plain,
    ( spl7_8
  <=> ! [X0] :
        ( r2_waybel_0(sK0,sK1,X0)
        | r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f460,plain,
    ( spl7_19
  <=> ! [X1,X0] :
        ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0)
        | ~ r2_waybel_0(sK0,sK1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f537,plain,
    ( spl7_30
  <=> u1_struct_0(sK0) = k6_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f550,plain,
    ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0)
    | ~ spl7_8
    | ~ spl7_19
    | ~ spl7_30 ),
    inference(superposition,[],[f466,f538])).

fof(f538,plain,
    ( u1_struct_0(sK0) = k6_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl7_30 ),
    inference(avatar_component_clause,[],[f537])).

fof(f466,plain,
    ( ! [X0] :
        ( r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0))
        | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,sK4(u1_struct_0(sK1)))),X0) )
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(resolution,[],[f464,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f5,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK4(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f5,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f464,plain,
    ( ! [X4,X3] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK1))
        | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X3,X4)),X3)
        | r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X3)) )
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(resolution,[],[f461,f140])).

fof(f140,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK0,sK1,X0)
        | r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0)) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f461,plain,
    ( ! [X0,X1] :
        ( ~ r2_waybel_0(sK0,sK1,X0)
        | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f460])).

fof(f543,plain,
    ( spl7_30
    | ~ spl7_28
    | spl7_31
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f535,f524,f541,f524,f537])).

fof(f524,plain,
    ( spl7_28
  <=> r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f535,plain,
    ( r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0)
    | ~ r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k6_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl7_28 ),
    inference(resolution,[],[f525,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | k6_subset_1(X0,X1) = X2 ) ),
    inference(definition_unfolding,[],[f69,f61])).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(sK6(X0,X1,X2),X0)
      | ~ r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK6(X0,X1,X2),X1)
            | ~ r2_hidden(sK6(X0,X1,X2),X0)
            | ~ r2_hidden(sK6(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
              & r2_hidden(sK6(X0,X1,X2),X0) )
            | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK6(X0,X1,X2),X1)
          | ~ r2_hidden(sK6(X0,X1,X2),X0)
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(sK6(X0,X1,X2),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f525,plain,
    ( r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f524])).

fof(f527,plain,
    ( spl7_28
    | ~ spl7_17
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f516,f493,f267,f524])).

fof(f267,plain,
    ( spl7_17
  <=> ! [X4] : ~ r2_hidden(X4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f493,plain,
    ( spl7_24
  <=> ! [X1] :
        ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,sK4(u1_struct_0(sK1)))),X1)
        | r2_hidden(sK6(u1_struct_0(sK0),X1,u1_struct_0(sK0)),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f516,plain,
    ( r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl7_17
    | ~ spl7_24 ),
    inference(resolution,[],[f494,f268])).

fof(f268,plain,
    ( ! [X4] : ~ r2_hidden(X4,k1_xboole_0)
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f267])).

fof(f494,plain,
    ( ! [X1] :
        ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,sK4(u1_struct_0(sK1)))),X1)
        | r2_hidden(sK6(u1_struct_0(sK0),X1,u1_struct_0(sK0)),u1_struct_0(sK0)) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f493])).

fof(f496,plain,
    ( spl7_24
    | spl7_1
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f480,f460,f139,f80,f493])).

fof(f480,plain,
    ( ! [X1] :
        ( r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
        | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,sK4(u1_struct_0(sK1)))),X1)
        | r2_hidden(sK6(u1_struct_0(sK0),X1,u1_struct_0(sK0)),u1_struct_0(sK0)) )
    | ~ spl7_8
    | ~ spl7_19 ),
    inference(superposition,[],[f466,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k6_subset_1(X0,X1) = X0
      | r2_hidden(sK6(X0,X1,X0),X0) ) ),
    inference(factoring,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | r2_hidden(sK6(X0,X1,X2),X0)
      | k6_subset_1(X0,X1) = X2 ) ),
    inference(definition_unfolding,[],[f67,f61])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X0)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f462,plain,
    ( spl7_3
    | spl7_19
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f458,f455,f84,f460,f88])).

fof(f88,plain,
    ( spl7_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f84,plain,
    ( spl7_2
  <=> l1_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f455,plain,
    ( spl7_18
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | r2_hidden(k2_waybel_0(sK0,X1,sK3(sK0,X1,X2,X0)),X2)
        | v2_struct_0(X1)
        | ~ l1_waybel_0(X1,sK0)
        | ~ r2_waybel_0(sK0,X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f458,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0)
        | v2_struct_0(sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ r2_waybel_0(sK0,sK1,X0) )
    | ~ spl7_2
    | ~ spl7_18 ),
    inference(resolution,[],[f456,f85])).

fof(f85,plain,
    ( l1_waybel_0(sK1,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f456,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_waybel_0(X1,sK0)
        | r2_hidden(k2_waybel_0(sK0,X1,sK3(sK0,X1,X2,X0)),X2)
        | v2_struct_0(X1)
        | ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ r2_waybel_0(sK0,X1,X2) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f455])).

fof(f457,plain,
    ( spl7_5
    | spl7_18
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f453,f92,f455,f96])).

fof(f96,plain,
    ( spl7_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f92,plain,
    ( spl7_4
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f453,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ r2_waybel_0(sK0,X1,X2)
        | ~ l1_waybel_0(X1,sK0)
        | v2_struct_0(X1)
        | r2_hidden(k2_waybel_0(sK0,X1,sK3(sK0,X1,X2,X0)),X2)
        | v2_struct_0(sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f54,f93])).

fof(f93,plain,
    ( l1_struct_0(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f92])).

fof(f54,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ r2_waybel_0(X0,X1,X2)
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ( ! [X4] :
                      ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
                      & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
                      & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f31,f33,f32])).

% (28442)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
              | ~ r1_orders_2(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
            | ~ r1_orders_2(X1,sK2(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X5,X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
          & r1_orders_2(X1,X5,X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2)
        & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5))
        & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X5] :
                    ( ? [X6] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X6),X2)
                        & r1_orders_2(X1,X5,X6)
                        & m1_subset_1(X6,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | ? [X3] :
                    ( ! [X4] :
                        ( ~ r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        | ~ r1_orders_2(X1,X3,X4)
                        | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                    & m1_subset_1(X3,u1_struct_0(X1)) ) )
              & ( ! [X3] :
                    ( ? [X4] :
                        ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                        & r1_orders_2(X1,X3,X4)
                        & m1_subset_1(X4,u1_struct_0(X1)) )
                    | ~ m1_subset_1(X3,u1_struct_0(X1)) )
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X1))
                 => ? [X4] :
                      ( r2_hidden(k2_waybel_0(X0,X1,X4),X2)
                      & r1_orders_2(X1,X3,X4)
                      & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).

fof(f280,plain,
    ( ~ spl7_6
    | ~ spl7_16 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f101,f274])).

fof(f274,plain,
    ( ! [X7] : ~ v1_xboole_0(X7)
    | ~ spl7_16 ),
    inference(resolution,[],[f265,f59])).

fof(f265,plain,
    ( ! [X2,X3] : r2_hidden(sK6(X2,X3,k1_xboole_0),X2)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl7_16
  <=> ! [X3,X2] : r2_hidden(sK6(X2,X3,k1_xboole_0),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f101,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f269,plain,
    ( spl7_16
    | spl7_17
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f262,f185,f100,f267,f264])).

fof(f185,plain,
    ( spl7_14
  <=> ! [X10] :
        ( r2_hidden(sK6(X10,X10,X10),X10)
        | k1_xboole_0 = X10
        | k1_xboole_0 = k6_subset_1(X10,X10) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f262,plain,
    ( ! [X4,X2,X3] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | r2_hidden(sK6(X2,X3,k1_xboole_0),X2) )
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f116,f257])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k1_xboole_0)
        | ~ r2_hidden(X1,X0) )
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(superposition,[],[f77,f256])).

fof(f256,plain,
    ( ! [X0] : k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)
    | ~ spl7_6
    | ~ spl7_14 ),
    inference(resolution,[],[f247,f101])).

fof(f247,plain,
    ( ! [X8,X9] :
        ( ~ v1_xboole_0(X8)
        | k1_xboole_0 = k6_subset_1(X8,X9) )
    | ~ spl7_14 ),
    inference(resolution,[],[f202,f59])).

fof(f202,plain,
    ( ! [X12,X11] :
        ( r2_hidden(sK6(k6_subset_1(X11,X12),k6_subset_1(X11,X12),k6_subset_1(X11,X12)),X11)
        | k1_xboole_0 = k6_subset_1(X11,X12) )
    | ~ spl7_14 ),
    inference(resolution,[],[f194,f78])).

fof(f78,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k6_subset_1(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f64,f61])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f194,plain,
    ( ! [X1] :
        ( r2_hidden(sK6(X1,X1,X1),X1)
        | k1_xboole_0 = X1 )
    | ~ spl7_14 ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( ! [X1] :
        ( k1_xboole_0 = X1
        | k1_xboole_0 = X1
        | r2_hidden(sK6(X1,X1,X1),X1)
        | r2_hidden(sK6(X1,X1,X1),X1) )
    | ~ spl7_14 ),
    inference(superposition,[],[f186,f108])).

fof(f186,plain,
    ( ! [X10] :
        ( k1_xboole_0 = k6_subset_1(X10,X10)
        | k1_xboole_0 = X10
        | r2_hidden(sK6(X10,X10,X10),X10) )
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f185])).

fof(f77,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k6_subset_1(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k6_subset_1(X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f65,f61])).

fof(f65,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f116,plain,
    ( ! [X4,X2,X3] :
        ( ~ r2_hidden(X4,k1_xboole_0)
        | r2_hidden(X4,X2)
        | r2_hidden(sK6(X2,X3,k1_xboole_0),X2) )
    | ~ spl7_6 ),
    inference(superposition,[],[f78,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k6_subset_1(X0,X1)
        | r2_hidden(sK6(X0,X1,k1_xboole_0),X0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f105,f101])).

fof(f105,plain,(
    ! [X6,X8,X7] :
      ( ~ v1_xboole_0(X8)
      | k6_subset_1(X6,X7) = X8
      | r2_hidden(sK6(X6,X7,X8),X6) ) ),
    inference(resolution,[],[f72,f59])).

fof(f187,plain,
    ( ~ spl7_6
    | spl7_14
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f178,f100,f185,f100])).

fof(f178,plain,
    ( ! [X10] :
        ( r2_hidden(sK6(X10,X10,X10),X10)
        | k1_xboole_0 = k6_subset_1(X10,X10)
        | k1_xboole_0 = X10
        | ~ v1_xboole_0(k1_xboole_0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f120,f59])).

fof(f120,plain,
    ( ! [X0] :
        ( r2_hidden(sK6(X0,X0,k1_xboole_0),k1_xboole_0)
        | r2_hidden(sK6(X0,X0,X0),X0)
        | k1_xboole_0 = k6_subset_1(X0,X0)
        | k1_xboole_0 = X0 )
    | ~ spl7_6 ),
    inference(resolution,[],[f114,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1,X2),X1)
      | k6_subset_1(X0,X1) = X2
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(definition_unfolding,[],[f68,f61])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK6(X0,X1,X2),X1)
      | r2_hidden(sK6(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f114,plain,
    ( ! [X2,X3] :
        ( r2_hidden(sK6(X2,X3,k1_xboole_0),X2)
        | k1_xboole_0 = X2
        | r2_hidden(sK6(X2,X3,X2),X2) )
    | ~ spl7_6 ),
    inference(superposition,[],[f113,f108])).

fof(f141,plain,
    ( spl7_3
    | spl7_8
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f136,f133,f84,f139,f88])).

fof(f133,plain,
    ( spl7_7
  <=> ! [X1,X0] :
        ( r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
        | r2_waybel_0(sK0,X0,X1)
        | v2_struct_0(X0)
        | ~ l1_waybel_0(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f136,plain,
    ( ! [X0] :
        ( r2_waybel_0(sK0,sK1,X0)
        | v2_struct_0(sK1)
        | r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0)) )
    | ~ spl7_2
    | ~ spl7_7 ),
    inference(resolution,[],[f134,f85])).

fof(f134,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(X0,sK0)
        | r2_waybel_0(sK0,X0,X1)
        | v2_struct_0(X0)
        | r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( spl7_5
    | spl7_7
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f130,f92,f133,f96])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))
        | ~ l1_waybel_0(X0,sK0)
        | v2_struct_0(X0)
        | r2_waybel_0(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl7_4 ),
    inference(resolution,[],[f51,f93])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_struct_0(X0)
      | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
      | ~ l1_waybel_0(X1,X0)
      | v2_struct_0(X1)
      | r2_waybel_0(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_0(X0,X1,X2)
                | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
              & ( ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))
                | ~ r2_waybel_0(X0,X1,X2) ) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) )
          | ~ l1_waybel_0(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( r2_waybel_0(X0,X1,X2)
            <=> ~ r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).

fof(f102,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f49,f100])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f98,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
    & l1_waybel_0(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
            & l1_waybel_0(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r1_waybel_0(sK0,X1,u1_struct_0(sK0))
          & l1_waybel_0(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ r1_waybel_0(sK0,X1,u1_struct_0(sK0))
        & l1_waybel_0(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0))
      & l1_waybel_0(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_waybel_0(X0,X1,u1_struct_0(X0))
          & l1_waybel_0(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l1_waybel_0(X1,X0)
              & v7_waybel_0(X1)
              & v4_orders_2(X1)
              & ~ v2_struct_0(X1) )
           => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => r1_waybel_0(X0,X1,u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).

fof(f94,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f45,f92])).

fof(f45,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f90,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f46,f88])).

fof(f46,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f86,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f47,f84])).

fof(f47,plain,(
    l1_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f82,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f48,f80])).

fof(f48,plain,(
    ~ r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:47:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (28427)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.49  % (28427)Refutation not found, incomplete strategy% (28427)------------------------------
% 0.21/0.49  % (28427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (28427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (28427)Memory used [KB]: 1663
% 0.21/0.49  % (28427)Time elapsed: 0.003 s
% 0.21/0.49  % (28427)------------------------------
% 0.21/0.49  % (28427)------------------------------
% 0.21/0.49  % (28446)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (28430)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (28434)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (28437)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (28428)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (28438)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (28446)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f633,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f82,f86,f90,f94,f98,f102,f135,f141,f187,f269,f280,f457,f462,f496,f527,f543,f574,f594,f632])).
% 0.21/0.53  % (28438)Refutation not found, incomplete strategy% (28438)------------------------------
% 0.21/0.53  % (28438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28438)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (28438)Memory used [KB]: 10618
% 0.21/0.53  % (28438)Time elapsed: 0.113 s
% 0.21/0.53  % (28438)------------------------------
% 0.21/0.53  % (28438)------------------------------
% 0.21/0.53  fof(f632,plain,(
% 0.21/0.53    ~spl7_6 | ~spl7_35),
% 0.21/0.53    inference(avatar_split_clause,[],[f623,f572,f100])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    spl7_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.53  fof(f572,plain,(
% 0.21/0.53    spl7_35 <=> r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).
% 0.21/0.53  fof(f623,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | ~spl7_35),
% 0.21/0.53    inference(resolution,[],[f573,f59])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.53  fof(f573,plain,(
% 0.21/0.53    r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0) | ~spl7_35),
% 0.21/0.53    inference(avatar_component_clause,[],[f572])).
% 0.21/0.53  fof(f594,plain,(
% 0.21/0.53    ~spl7_6 | ~spl7_31),
% 0.21/0.53    inference(avatar_split_clause,[],[f582,f541,f100])).
% 0.21/0.53  fof(f541,plain,(
% 0.21/0.53    spl7_31 <=> r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.53  fof(f582,plain,(
% 0.21/0.53    ~v1_xboole_0(k1_xboole_0) | ~spl7_31),
% 0.21/0.53    inference(resolution,[],[f542,f59])).
% 0.21/0.53  fof(f542,plain,(
% 0.21/0.53    r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0) | ~spl7_31),
% 0.21/0.53    inference(avatar_component_clause,[],[f541])).
% 0.21/0.53  fof(f574,plain,(
% 0.21/0.53    spl7_35 | spl7_1 | ~spl7_8 | ~spl7_19 | ~spl7_30),
% 0.21/0.53    inference(avatar_split_clause,[],[f550,f537,f460,f139,f80,f572])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    spl7_1 <=> r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.53  fof(f139,plain,(
% 0.21/0.53    spl7_8 <=> ! [X0] : (r2_waybel_0(sK0,sK1,X0) | r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.53  fof(f460,plain,(
% 0.21/0.53    spl7_19 <=> ! [X1,X0] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0) | ~r2_waybel_0(sK0,sK1,X0) | ~m1_subset_1(X1,u1_struct_0(sK1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.21/0.53  fof(f537,plain,(
% 0.21/0.53    spl7_30 <=> u1_struct_0(sK0) = k6_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).
% 0.21/0.53  fof(f550,plain,(
% 0.21/0.53    r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,k1_xboole_0,sK4(u1_struct_0(sK1)))),k1_xboole_0) | (~spl7_8 | ~spl7_19 | ~spl7_30)),
% 0.21/0.53    inference(superposition,[],[f466,f538])).
% 0.21/0.53  fof(f538,plain,(
% 0.21/0.53    u1_struct_0(sK0) = k6_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~spl7_30),
% 0.21/0.53    inference(avatar_component_clause,[],[f537])).
% 0.21/0.53  fof(f466,plain,(
% 0.21/0.53    ( ! [X0] : (r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,sK4(u1_struct_0(sK1)))),X0)) ) | (~spl7_8 | ~spl7_19)),
% 0.21/0.53    inference(resolution,[],[f464,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(sK4(X0),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ! [X0] : m1_subset_1(sK4(X0),X0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f5,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK4(X0),X0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 0.21/0.53  fof(f464,plain,(
% 0.21/0.53    ( ! [X4,X3] : (~m1_subset_1(X4,u1_struct_0(sK1)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X3,X4)),X3) | r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X3))) ) | (~spl7_8 | ~spl7_19)),
% 0.21/0.53    inference(resolution,[],[f461,f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ( ! [X0] : (r2_waybel_0(sK0,sK1,X0) | r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0))) ) | ~spl7_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f139])).
% 0.21/0.53  fof(f461,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_waybel_0(sK0,sK1,X0) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0) | ~m1_subset_1(X1,u1_struct_0(sK1))) ) | ~spl7_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f460])).
% 0.21/0.53  fof(f543,plain,(
% 0.21/0.53    spl7_30 | ~spl7_28 | spl7_31 | ~spl7_28),
% 0.21/0.53    inference(avatar_split_clause,[],[f535,f524,f541,f524,f537])).
% 0.21/0.53  fof(f524,plain,(
% 0.21/0.53    spl7_28 <=> r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.21/0.53  fof(f535,plain,(
% 0.21/0.53    r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),k1_xboole_0) | ~r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = k6_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~spl7_28),
% 0.21/0.53    inference(resolution,[],[f525,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | k6_subset_1(X0,X1) = X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f69,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f41,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(sK6(X0,X1,X2),X0) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((~r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(sK6(X0,X1,X2),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(rectify,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(flattening,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.53  fof(f525,plain,(
% 0.21/0.53    r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl7_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f524])).
% 0.21/0.53  fof(f527,plain,(
% 0.21/0.53    spl7_28 | ~spl7_17 | ~spl7_24),
% 0.21/0.53    inference(avatar_split_clause,[],[f516,f493,f267,f524])).
% 0.21/0.53  fof(f267,plain,(
% 0.21/0.53    spl7_17 <=> ! [X4] : ~r2_hidden(X4,k1_xboole_0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.21/0.53  fof(f493,plain,(
% 0.21/0.53    spl7_24 <=> ! [X1] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,sK4(u1_struct_0(sK1)))),X1) | r2_hidden(sK6(u1_struct_0(sK0),X1,u1_struct_0(sK0)),u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.53  fof(f516,plain,(
% 0.21/0.53    r2_hidden(sK6(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)),u1_struct_0(sK0)) | (~spl7_17 | ~spl7_24)),
% 0.21/0.53    inference(resolution,[],[f494,f268])).
% 0.21/0.53  fof(f268,plain,(
% 0.21/0.53    ( ! [X4] : (~r2_hidden(X4,k1_xboole_0)) ) | ~spl7_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f267])).
% 0.21/0.53  fof(f494,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,sK4(u1_struct_0(sK1)))),X1) | r2_hidden(sK6(u1_struct_0(sK0),X1,u1_struct_0(sK0)),u1_struct_0(sK0))) ) | ~spl7_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f493])).
% 0.21/0.53  fof(f496,plain,(
% 0.21/0.53    spl7_24 | spl7_1 | ~spl7_8 | ~spl7_19),
% 0.21/0.53    inference(avatar_split_clause,[],[f480,f460,f139,f80,f493])).
% 0.21/0.53  fof(f480,plain,(
% 0.21/0.53    ( ! [X1] : (r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) | r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X1,sK4(u1_struct_0(sK1)))),X1) | r2_hidden(sK6(u1_struct_0(sK0),X1,u1_struct_0(sK0)),u1_struct_0(sK0))) ) | (~spl7_8 | ~spl7_19)),
% 0.21/0.53    inference(superposition,[],[f466,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k6_subset_1(X0,X1) = X0 | r2_hidden(sK6(X0,X1,X0),X0)) )),
% 0.21/0.53    inference(factoring,[],[f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | r2_hidden(sK6(X0,X1,X2),X0) | k6_subset_1(X0,X1) = X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f67,f61])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X0) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f43])).
% 0.21/0.53  fof(f462,plain,(
% 0.21/0.53    spl7_3 | spl7_19 | ~spl7_2 | ~spl7_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f458,f455,f84,f460,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    spl7_3 <=> v2_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    spl7_2 <=> l1_waybel_0(sK1,sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.53  fof(f455,plain,(
% 0.21/0.53    spl7_18 <=> ! [X1,X0,X2] : (~m1_subset_1(X0,u1_struct_0(X1)) | r2_hidden(k2_waybel_0(sK0,X1,sK3(sK0,X1,X2,X0)),X2) | v2_struct_0(X1) | ~l1_waybel_0(X1,sK0) | ~r2_waybel_0(sK0,X1,X2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.53  fof(f458,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(k2_waybel_0(sK0,sK1,sK3(sK0,sK1,X0,X1)),X0) | v2_struct_0(sK1) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~r2_waybel_0(sK0,sK1,X0)) ) | (~spl7_2 | ~spl7_18)),
% 0.21/0.53    inference(resolution,[],[f456,f85])).
% 0.21/0.53  fof(f85,plain,(
% 0.21/0.53    l1_waybel_0(sK1,sK0) | ~spl7_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f84])).
% 0.21/0.53  fof(f456,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_waybel_0(X1,sK0) | r2_hidden(k2_waybel_0(sK0,X1,sK3(sK0,X1,X2,X0)),X2) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_waybel_0(sK0,X1,X2)) ) | ~spl7_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f455])).
% 0.21/0.53  fof(f457,plain,(
% 0.21/0.53    spl7_5 | spl7_18 | ~spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f453,f92,f455,f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    spl7_5 <=> v2_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl7_4 <=> l1_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.53  fof(f453,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_waybel_0(sK0,X1,X2) | ~l1_waybel_0(X1,sK0) | v2_struct_0(X1) | r2_hidden(k2_waybel_0(sK0,X1,sK3(sK0,X1,X2,X0)),X2) | v2_struct_0(sK0)) ) | ~spl7_4),
% 0.21/0.53    inference(resolution,[],[f54,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    l1_struct_0(sK0) | ~spl7_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f92])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X5,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~r2_waybel_0(X0,X1,X2) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)))) & (! [X5] : ((r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f31,f33,f32])).
% 0.21/0.53  % (28442)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,sK2(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X5,X2,X1,X0] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(k2_waybel_0(X0,X1,sK3(X0,X1,X2,X5)),X2) & r1_orders_2(X1,X5,sK3(X0,X1,X2,X5)) & m1_subset_1(sK3(X0,X1,X2,X5),u1_struct_0(X1))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X5] : (? [X6] : (r2_hidden(k2_waybel_0(X0,X1,X6),X2) & r1_orders_2(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(rectify,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | ? [X3] : (! [X4] : (~r2_hidden(k2_waybel_0(X0,X1,X4),X2) | ~r1_orders_2(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X1)) => ? [X4] : (r2_hidden(k2_waybel_0(X0,X1,X4),X2) & r1_orders_2(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1)))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_waybel_0)).
% 0.21/0.53  fof(f280,plain,(
% 0.21/0.53    ~spl7_6 | ~spl7_16),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f279])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    $false | (~spl7_6 | ~spl7_16)),
% 0.21/0.53    inference(subsumption_resolution,[],[f101,f274])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    ( ! [X7] : (~v1_xboole_0(X7)) ) | ~spl7_16),
% 0.21/0.53    inference(resolution,[],[f265,f59])).
% 0.21/0.53  fof(f265,plain,(
% 0.21/0.53    ( ! [X2,X3] : (r2_hidden(sK6(X2,X3,k1_xboole_0),X2)) ) | ~spl7_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f264])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    spl7_16 <=> ! [X3,X2] : r2_hidden(sK6(X2,X3,k1_xboole_0),X2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0) | ~spl7_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f100])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    spl7_16 | spl7_17 | ~spl7_6 | ~spl7_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f262,f185,f100,f267,f264])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    spl7_14 <=> ! [X10] : (r2_hidden(sK6(X10,X10,X10),X10) | k1_xboole_0 = X10 | k1_xboole_0 = k6_subset_1(X10,X10))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    ( ! [X4,X2,X3] : (~r2_hidden(X4,k1_xboole_0) | r2_hidden(sK6(X2,X3,k1_xboole_0),X2)) ) | (~spl7_6 | ~spl7_14)),
% 0.21/0.53    inference(subsumption_resolution,[],[f116,f257])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,X0)) ) | (~spl7_6 | ~spl7_14)),
% 0.21/0.53    inference(superposition,[],[f77,f256])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k6_subset_1(k1_xboole_0,X0)) ) | (~spl7_6 | ~spl7_14)),
% 0.21/0.53    inference(resolution,[],[f247,f101])).
% 0.21/0.53  fof(f247,plain,(
% 0.21/0.53    ( ! [X8,X9] : (~v1_xboole_0(X8) | k1_xboole_0 = k6_subset_1(X8,X9)) ) | ~spl7_14),
% 0.21/0.53    inference(resolution,[],[f202,f59])).
% 0.21/0.53  fof(f202,plain,(
% 0.21/0.53    ( ! [X12,X11] : (r2_hidden(sK6(k6_subset_1(X11,X12),k6_subset_1(X11,X12),k6_subset_1(X11,X12)),X11) | k1_xboole_0 = k6_subset_1(X11,X12)) ) | ~spl7_14),
% 0.21/0.53    inference(resolution,[],[f194,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k6_subset_1(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f64,f61])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f43])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(sK6(X1,X1,X1),X1) | k1_xboole_0 = X1) ) | ~spl7_14),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f188])).
% 0.21/0.53  fof(f188,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = X1 | k1_xboole_0 = X1 | r2_hidden(sK6(X1,X1,X1),X1) | r2_hidden(sK6(X1,X1,X1),X1)) ) | ~spl7_14),
% 0.21/0.53    inference(superposition,[],[f186,f108])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    ( ! [X10] : (k1_xboole_0 = k6_subset_1(X10,X10) | k1_xboole_0 = X10 | r2_hidden(sK6(X10,X10,X10),X10)) ) | ~spl7_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f185])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k6_subset_1(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k6_subset_1(X0,X1) != X2) )),
% 0.21/0.53    inference(definition_unfolding,[],[f65,f61])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f43])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    ( ! [X4,X2,X3] : (~r2_hidden(X4,k1_xboole_0) | r2_hidden(X4,X2) | r2_hidden(sK6(X2,X3,k1_xboole_0),X2)) ) | ~spl7_6),
% 0.21/0.53    inference(superposition,[],[f78,f113])).
% 0.21/0.53  fof(f113,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k1_xboole_0 = k6_subset_1(X0,X1) | r2_hidden(sK6(X0,X1,k1_xboole_0),X0)) ) | ~spl7_6),
% 0.21/0.53    inference(resolution,[],[f105,f101])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    ( ! [X6,X8,X7] : (~v1_xboole_0(X8) | k6_subset_1(X6,X7) = X8 | r2_hidden(sK6(X6,X7,X8),X6)) )),
% 0.21/0.53    inference(resolution,[],[f72,f59])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    ~spl7_6 | spl7_14 | ~spl7_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f178,f100,f185,f100])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X10] : (r2_hidden(sK6(X10,X10,X10),X10) | k1_xboole_0 = k6_subset_1(X10,X10) | k1_xboole_0 = X10 | ~v1_xboole_0(k1_xboole_0)) ) | ~spl7_6),
% 0.21/0.53    inference(resolution,[],[f120,f59])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK6(X0,X0,k1_xboole_0),k1_xboole_0) | r2_hidden(sK6(X0,X0,X0),X0) | k1_xboole_0 = k6_subset_1(X0,X0) | k1_xboole_0 = X0) ) | ~spl7_6),
% 0.21/0.53    inference(resolution,[],[f114,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK6(X0,X1,X2),X1) | k6_subset_1(X0,X1) = X2 | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(definition_unfolding,[],[f68,f61])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = X2 | ~r2_hidden(sK6(X0,X1,X2),X1) | r2_hidden(sK6(X0,X1,X2),X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f43])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    ( ! [X2,X3] : (r2_hidden(sK6(X2,X3,k1_xboole_0),X2) | k1_xboole_0 = X2 | r2_hidden(sK6(X2,X3,X2),X2)) ) | ~spl7_6),
% 0.21/0.53    inference(superposition,[],[f113,f108])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    spl7_3 | spl7_8 | ~spl7_2 | ~spl7_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f136,f133,f84,f139,f88])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    spl7_7 <=> ! [X1,X0] : (r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | r2_waybel_0(sK0,X0,X1) | v2_struct_0(X0) | ~l1_waybel_0(X0,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    ( ! [X0] : (r2_waybel_0(sK0,sK1,X0) | v2_struct_0(sK1) | r1_waybel_0(sK0,sK1,k6_subset_1(u1_struct_0(sK0),X0))) ) | (~spl7_2 | ~spl7_7)),
% 0.21/0.53    inference(resolution,[],[f134,f85])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | r2_waybel_0(sK0,X0,X1) | v2_struct_0(X0) | r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1))) ) | ~spl7_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f133])).
% 0.21/0.53  fof(f135,plain,(
% 0.21/0.53    spl7_5 | spl7_7 | ~spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f130,f92,f133,f96])).
% 0.21/0.53  fof(f130,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_waybel_0(sK0,X0,k6_subset_1(u1_struct_0(sK0),X1)) | ~l1_waybel_0(X0,sK0) | v2_struct_0(X0) | r2_waybel_0(sK0,X0,X1) | v2_struct_0(sK0)) ) | ~spl7_4),
% 0.21/0.53    inference(resolution,[],[f51,f93])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~l1_struct_0(X0) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1) | r2_waybel_0(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_0(X0,X1,X2) | r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) & (~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)) | ~r2_waybel_0(X0,X1,X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | ~l1_waybel_0(X1,X0) | v2_struct_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2))) | (~l1_waybel_0(X1,X0) | v2_struct_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (r2_waybel_0(X0,X1,X2) <=> ~r1_waybel_0(X0,X1,k6_subset_1(u1_struct_0(X0),X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_waybel_0)).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    spl7_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f49,f100])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    v1_xboole_0(k1_xboole_0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.53  fof(f98,plain,(
% 0.21/0.53    ~spl7_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f44,f96])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f27,f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) & l1_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ? [X1] : (~r1_waybel_0(sK0,X1,u1_struct_0(sK0)) & l1_waybel_0(X1,sK0) & ~v2_struct_0(X1)) => (~r1_waybel_0(sK0,sK1,u1_struct_0(sK0)) & l1_waybel_0(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) & l1_struct_0(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (~r1_waybel_0(X0,X1,u1_struct_0(X0)) & (l1_waybel_0(X1,X0) & ~v2_struct_0(X1))) & (l1_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.53    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.53  fof(f11,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.53    inference(negated_conjecture,[],[f10])).
% 0.21/0.53  fof(f10,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => r1_waybel_0(X0,X1,u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_yellow_6)).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl7_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f45,f92])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    l1_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    ~spl7_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f46,f88])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ~v2_struct_0(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl7_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f47,f84])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    l1_waybel_0(sK1,sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    ~spl7_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f48,f80])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ~r1_waybel_0(sK0,sK1,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (28446)------------------------------
% 0.21/0.53  % (28446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (28446)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (28446)Memory used [KB]: 11129
% 0.21/0.53  % (28446)Time elapsed: 0.106 s
% 0.21/0.53  % (28446)------------------------------
% 0.21/0.53  % (28446)------------------------------
% 0.21/0.53  % (28453)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (28455)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (28426)Success in time 0.174 s
%------------------------------------------------------------------------------
