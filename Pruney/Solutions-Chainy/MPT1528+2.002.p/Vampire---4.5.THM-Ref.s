%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 300 expanded)
%              Number of leaves         :   24 ( 116 expanded)
%              Depth                    :   10
%              Number of atoms          :  424 (1106 expanded)
%              Number of equality atoms :   33 ( 139 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f362,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f77,f92,f103,f112,f117,f139,f205,f248,f251,f345,f348,f351])).

fof(f351,plain,
    ( ~ spl5_6
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f350])).

fof(f350,plain,
    ( $false
    | ~ spl5_6
    | spl5_15 ),
    inference(subsumption_resolution,[],[f349,f268])).

fof(f268,plain,
    ( ! [X0] : r2_hidden(sK2(sK0,k1_xboole_0,sK1),X0)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f38,f102,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f102,plain,
    ( r2_hidden(sK2(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_6
  <=> r2_hidden(sK2(sK0,k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f349,plain,
    ( ~ r2_hidden(sK2(sK0,k1_xboole_0,sK1),u1_orders_2(sK0))
    | ~ spl5_6
    | spl5_15 ),
    inference(forward_demodulation,[],[f344,f285])).

fof(f285,plain,
    ( ! [X0] : sK2(sK0,k1_xboole_0,sK1) = X0
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f268,f57])).

fof(f57,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK4(X0,X1) != X0
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( sK4(X0,X1) = X0
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK4(X0,X1) != X0
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( sK4(X0,X1) = X0
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f344,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2(sK0,k1_xboole_0,sK1)),u1_orders_2(sK0))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f342])).

fof(f342,plain,
    ( spl5_15
  <=> r2_hidden(k4_tarski(sK1,sK2(sK0,k1_xboole_0,sK1)),u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f348,plain,
    ( ~ spl5_5
    | spl5_15 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | ~ spl5_5
    | spl5_15 ),
    inference(subsumption_resolution,[],[f346,f127])).

fof(f127,plain,
    ( ! [X0] : r2_hidden(sK3(sK0,k1_xboole_0,sK1),X0)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f38,f91,f49])).

fof(f91,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_5
  <=> r2_hidden(sK3(sK0,k1_xboole_0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f346,plain,
    ( ~ r2_hidden(sK3(sK0,k1_xboole_0,sK1),u1_orders_2(sK0))
    | ~ spl5_5
    | spl5_15 ),
    inference(forward_demodulation,[],[f344,f231])).

fof(f231,plain,
    ( ! [X0] : sK3(sK0,k1_xboole_0,sK1) = X0
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f127,f57])).

fof(f345,plain,
    ( ~ spl5_15
    | ~ spl5_1
    | ~ spl5_2
    | spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f221,f114,f109,f65,f60,f342])).

fof(f60,plain,
    ( spl5_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f65,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f109,plain,
    ( spl5_7
  <=> r1_orders_2(sK0,sK1,sK2(sK0,k1_xboole_0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f114,plain,
    ( spl5_8
  <=> m1_subset_1(sK2(sK0,k1_xboole_0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f221,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2(sK0,k1_xboole_0,sK1)),u1_orders_2(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | spl5_7
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f62,f67,f111,f116,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).

fof(f116,plain,
    ( m1_subset_1(sK2(sK0,k1_xboole_0,sK1),u1_struct_0(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f111,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2(sK0,k1_xboole_0,sK1))
    | spl5_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f67,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f62,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f251,plain,
    ( ~ spl5_5
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f250])).

fof(f250,plain,
    ( $false
    | ~ spl5_5
    | spl5_11 ),
    inference(subsumption_resolution,[],[f249,f126])).

fof(f126,plain,
    ( ! [X0] : m1_subset_1(sK3(sK0,k1_xboole_0,sK1),X0)
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f38,f91,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f249,plain,
    ( ~ m1_subset_1(sK3(sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_5
    | spl5_11 ),
    inference(forward_demodulation,[],[f247,f231])).

fof(f247,plain,
    ( ~ m1_subset_1(k1_tarski(sK2(sK0,k1_xboole_0,sK1)),k1_zfmisc_1(k1_xboole_0))
    | spl5_11 ),
    inference(avatar_component_clause,[],[f245])).

fof(f245,plain,
    ( spl5_11
  <=> m1_subset_1(k1_tarski(sK2(sK0,k1_xboole_0,sK1)),k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f248,plain,
    ( ~ spl5_11
    | spl5_6 ),
    inference(avatar_split_clause,[],[f217,f100,f245])).

fof(f217,plain,
    ( ~ m1_subset_1(k1_tarski(sK2(sK0,k1_xboole_0,sK1)),k1_zfmisc_1(k1_xboole_0))
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f56,f101,f49])).

fof(f101,plain,
    ( ~ r2_hidden(sK2(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f56,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f205,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9 ),
    inference(subsumption_resolution,[],[f203,f106])).

fof(f106,plain,
    ( ! [X0] : r2_hidden(sK2(sK0,k1_xboole_0,sK1),X0)
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f38,f102,f49])).

fof(f203,plain,
    ( ~ r2_hidden(sK2(sK0,k1_xboole_0,sK1),u1_orders_2(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_6
    | spl5_9 ),
    inference(forward_demodulation,[],[f192,f176])).

fof(f176,plain,
    ( ! [X0] : sK2(sK0,k1_xboole_0,sK1) = X0
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f106,f57])).

fof(f192,plain,
    ( ~ r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,sK1),sK1),u1_orders_2(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_5
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f62,f67,f138,f126,f40])).

fof(f138,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,k1_xboole_0,sK1),sK1)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl5_9
  <=> r1_orders_2(sK0,sK3(sK0,k1_xboole_0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f139,plain,
    ( ~ spl5_9
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f118,f70,f65,f60,f136])).

fof(f70,plain,
    ( spl5_3
  <=> r2_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f118,plain,
    ( ~ r1_orders_2(sK0,sK3(sK0,k1_xboole_0,sK1),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f62,f67,f72,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
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
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f72,plain,
    ( ~ r2_lattice3(sK0,k1_xboole_0,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f117,plain,
    ( spl5_8
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f94,f74,f65,f60,f114])).

fof(f74,plain,
    ( spl5_4
  <=> r1_lattice3(sK0,k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f94,plain,
    ( m1_subset_1(sK2(sK0,k1_xboole_0,sK1),u1_struct_0(sK0))
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f62,f67,f76,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
                & r2_hidden(sK2(X0,X1,X2),X1)
                & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).

% (7237)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (7216)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X2,X4)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r1_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X2,X3)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f76,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f112,plain,
    ( ~ spl5_7
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f93,f74,f65,f60,f109])).

fof(f93,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2(sK0,k1_xboole_0,sK1))
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f62,f67,f76,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK2(X0,X1,X2))
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f103,plain,
    ( spl5_6
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4 ),
    inference(avatar_split_clause,[],[f95,f74,f65,f60,f100])).

fof(f95,plain,
    ( r2_hidden(sK2(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f62,f67,f76,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f92,plain,
    ( spl5_5
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f85,f70,f65,f60,f89])).

fof(f85,plain,
    ( r2_hidden(sK3(sK0,k1_xboole_0,sK1),k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3 ),
    inference(unit_resulting_resolution,[],[f62,f72,f67,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f77,plain,
    ( ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f37,f74,f70])).

fof(f37,plain,
    ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
    | ~ r2_lattice3(sK0,k1_xboole_0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
      | ~ r2_lattice3(sK0,k1_xboole_0,sK1) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f20,f19])).

fof(f19,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
              | ~ r2_lattice3(X0,k1_xboole_0,X1) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ r1_lattice3(sK0,k1_xboole_0,X1)
            | ~ r2_lattice3(sK0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X1] :
        ( ( ~ r1_lattice3(sK0,k1_xboole_0,X1)
          | ~ r2_lattice3(sK0,k1_xboole_0,X1) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ r1_lattice3(sK0,k1_xboole_0,sK1)
        | ~ r2_lattice3(sK0,k1_xboole_0,sK1) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_lattice3(X0,k1_xboole_0,X1)
            | ~ r2_lattice3(X0,k1_xboole_0,X1) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( r1_lattice3(X0,k1_xboole_0,X1)
              & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r1_lattice3(X0,k1_xboole_0,X1)
            & r2_lattice3(X0,k1_xboole_0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).

fof(f68,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f36,f65])).

fof(f36,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f63,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f35,f60])).

fof(f35,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:45:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (7218)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.49  % (7227)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (7218)Refutation not found, incomplete strategy% (7218)------------------------------
% 0.22/0.50  % (7218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7233)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.50  % (7218)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (7218)Memory used [KB]: 6140
% 0.22/0.50  % (7218)Time elapsed: 0.082 s
% 0.22/0.50  % (7218)------------------------------
% 0.22/0.50  % (7218)------------------------------
% 0.22/0.50  % (7232)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.50  % (7236)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.50  % (7217)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (7228)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.50  % (7222)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.50  % (7213)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (7221)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.51  % (7230)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.51  % (7238)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.51  % (7234)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.51  % (7226)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.51  % (7219)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (7219)Refutation not found, incomplete strategy% (7219)------------------------------
% 0.22/0.52  % (7219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (7219)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (7219)Memory used [KB]: 10618
% 0.22/0.52  % (7219)Time elapsed: 0.092 s
% 0.22/0.52  % (7219)------------------------------
% 0.22/0.52  % (7219)------------------------------
% 0.22/0.52  % (7215)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.52  % (7224)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (7223)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.52  % (7220)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.52  % (7235)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (7220)Refutation not found, incomplete strategy% (7220)------------------------------
% 0.22/0.52  % (7220)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7220)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7220)Memory used [KB]: 1663
% 0.22/0.53  % (7220)Time elapsed: 0.116 s
% 0.22/0.53  % (7220)------------------------------
% 0.22/0.53  % (7220)------------------------------
% 0.22/0.53  % (7214)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % (7229)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.53  % (7236)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f362,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f63,f68,f77,f92,f103,f112,f117,f139,f205,f248,f251,f345,f348,f351])).
% 0.22/0.53  fof(f351,plain,(
% 0.22/0.53    ~spl5_6 | spl5_15),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f350])).
% 0.22/0.53  fof(f350,plain,(
% 0.22/0.53    $false | (~spl5_6 | spl5_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f349,f268])).
% 0.22/0.53  fof(f268,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK2(sK0,k1_xboole_0,sK1),X0)) ) | ~spl5_6),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f38,f102,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    r2_hidden(sK2(sK0,k1_xboole_0,sK1),k1_xboole_0) | ~spl5_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    spl5_6 <=> r2_hidden(sK2(sK0,k1_xboole_0,sK1),k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.22/0.53  fof(f349,plain,(
% 0.22/0.53    ~r2_hidden(sK2(sK0,k1_xboole_0,sK1),u1_orders_2(sK0)) | (~spl5_6 | spl5_15)),
% 0.22/0.53    inference(forward_demodulation,[],[f344,f285])).
% 0.22/0.53  fof(f285,plain,(
% 0.22/0.53    ( ! [X0] : (sK2(sK0,k1_xboole_0,sK1) = X0) ) | ~spl5_6),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f268,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 0.22/0.53    inference(equality_resolution,[],[f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f32,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK4(X0,X1) != X0 | ~r2_hidden(sK4(X0,X1),X1)) & (sK4(X0,X1) = X0 | r2_hidden(sK4(X0,X1),X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(rectify,[],[f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.53  fof(f344,plain,(
% 0.22/0.53    ~r2_hidden(k4_tarski(sK1,sK2(sK0,k1_xboole_0,sK1)),u1_orders_2(sK0)) | spl5_15),
% 0.22/0.53    inference(avatar_component_clause,[],[f342])).
% 0.22/0.53  fof(f342,plain,(
% 0.22/0.53    spl5_15 <=> r2_hidden(k4_tarski(sK1,sK2(sK0,k1_xboole_0,sK1)),u1_orders_2(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.53  fof(f348,plain,(
% 0.22/0.53    ~spl5_5 | spl5_15),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f347])).
% 0.22/0.53  fof(f347,plain,(
% 0.22/0.53    $false | (~spl5_5 | spl5_15)),
% 0.22/0.53    inference(subsumption_resolution,[],[f346,f127])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK3(sK0,k1_xboole_0,sK1),X0)) ) | ~spl5_5),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f38,f91,f49])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    r2_hidden(sK3(sK0,k1_xboole_0,sK1),k1_xboole_0) | ~spl5_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f89])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl5_5 <=> r2_hidden(sK3(sK0,k1_xboole_0,sK1),k1_xboole_0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.53  fof(f346,plain,(
% 0.22/0.53    ~r2_hidden(sK3(sK0,k1_xboole_0,sK1),u1_orders_2(sK0)) | (~spl5_5 | spl5_15)),
% 0.22/0.53    inference(forward_demodulation,[],[f344,f231])).
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    ( ! [X0] : (sK3(sK0,k1_xboole_0,sK1) = X0) ) | ~spl5_5),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f127,f57])).
% 0.22/0.53  fof(f345,plain,(
% 0.22/0.53    ~spl5_15 | ~spl5_1 | ~spl5_2 | spl5_7 | ~spl5_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f221,f114,f109,f65,f60,f342])).
% 0.22/0.53  fof(f60,plain,(
% 0.22/0.53    spl5_1 <=> l1_orders_2(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    spl5_2 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    spl5_7 <=> r1_orders_2(sK0,sK1,sK2(sK0,k1_xboole_0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    spl5_8 <=> m1_subset_1(sK2(sK0,k1_xboole_0,sK1),u1_struct_0(sK0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.53  fof(f221,plain,(
% 0.22/0.53    ~r2_hidden(k4_tarski(sK1,sK2(sK0,k1_xboole_0,sK1)),u1_orders_2(sK0)) | (~spl5_1 | ~spl5_2 | spl5_7 | ~spl5_8)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f62,f67,f111,f116,f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : (((r1_orders_2(X0,X1,X2) | ~r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) & (r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (! [X2] : ((r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_orders_2(X0,X1,X2) <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_orders_2)).
% 0.22/0.53  fof(f116,plain,(
% 0.22/0.53    m1_subset_1(sK2(sK0,k1_xboole_0,sK1),u1_struct_0(sK0)) | ~spl5_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f114])).
% 0.22/0.53  fof(f111,plain,(
% 0.22/0.53    ~r1_orders_2(sK0,sK1,sK2(sK0,k1_xboole_0,sK1)) | spl5_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f109])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f65])).
% 0.22/0.53  fof(f62,plain,(
% 0.22/0.53    l1_orders_2(sK0) | ~spl5_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f60])).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    ~spl5_5 | spl5_11),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f250])).
% 0.22/0.53  fof(f250,plain,(
% 0.22/0.53    $false | (~spl5_5 | spl5_11)),
% 0.22/0.53    inference(subsumption_resolution,[],[f249,f126])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(sK3(sK0,k1_xboole_0,sK1),X0)) ) | ~spl5_5),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f38,f91,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    ~m1_subset_1(sK3(sK0,k1_xboole_0,sK1),k1_zfmisc_1(k1_xboole_0)) | (~spl5_5 | spl5_11)),
% 0.22/0.53    inference(forward_demodulation,[],[f247,f231])).
% 0.22/0.53  fof(f247,plain,(
% 0.22/0.53    ~m1_subset_1(k1_tarski(sK2(sK0,k1_xboole_0,sK1)),k1_zfmisc_1(k1_xboole_0)) | spl5_11),
% 0.22/0.53    inference(avatar_component_clause,[],[f245])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    spl5_11 <=> m1_subset_1(k1_tarski(sK2(sK0,k1_xboole_0,sK1)),k1_zfmisc_1(k1_xboole_0))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    ~spl5_11 | spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f217,f100,f245])).
% 0.22/0.53  fof(f217,plain,(
% 0.22/0.53    ~m1_subset_1(k1_tarski(sK2(sK0,k1_xboole_0,sK1)),k1_zfmisc_1(k1_xboole_0)) | spl5_6),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f56,f101,f49])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ~r2_hidden(sK2(sK0,k1_xboole_0,sK1),k1_xboole_0) | spl5_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f100])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 0.22/0.53    inference(equality_resolution,[],[f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 0.22/0.53    inference(equality_resolution,[],[f51])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    ~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_6 | spl5_9),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f204])).
% 0.22/0.53  fof(f204,plain,(
% 0.22/0.53    $false | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_6 | spl5_9)),
% 0.22/0.53    inference(subsumption_resolution,[],[f203,f106])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ( ! [X0] : (r2_hidden(sK2(sK0,k1_xboole_0,sK1),X0)) ) | ~spl5_6),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f38,f102,f49])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    ~r2_hidden(sK2(sK0,k1_xboole_0,sK1),u1_orders_2(sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_5 | ~spl5_6 | spl5_9)),
% 0.22/0.53    inference(forward_demodulation,[],[f192,f176])).
% 0.22/0.53  fof(f176,plain,(
% 0.22/0.53    ( ! [X0] : (sK2(sK0,k1_xboole_0,sK1) = X0) ) | ~spl5_6),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f106,f57])).
% 0.22/0.53  fof(f192,plain,(
% 0.22/0.53    ~r2_hidden(k4_tarski(sK3(sK0,k1_xboole_0,sK1),sK1),u1_orders_2(sK0)) | (~spl5_1 | ~spl5_2 | ~spl5_5 | spl5_9)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f62,f67,f138,f126,f40])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    ~r1_orders_2(sK0,sK3(sK0,k1_xboole_0,sK1),sK1) | spl5_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f136])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    spl5_9 <=> r1_orders_2(sK0,sK3(sK0,k1_xboole_0,sK1),sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    ~spl5_9 | ~spl5_1 | ~spl5_2 | spl5_3),
% 0.22/0.53    inference(avatar_split_clause,[],[f118,f70,f65,f60,f136])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    spl5_3 <=> r2_lattice3(sK0,k1_xboole_0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ~r1_orders_2(sK0,sK3(sK0,k1_xboole_0,sK1),sK1) | (~spl5_1 | ~spl5_2 | spl5_3)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f62,f67,f72,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK3(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f28,f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(rectify,[],[f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(nnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ~r2_lattice3(sK0,k1_xboole_0,sK1) | spl5_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f70])).
% 0.22/0.53  fof(f117,plain,(
% 0.22/0.53    spl5_8 | ~spl5_1 | ~spl5_2 | spl5_4),
% 0.22/0.53    inference(avatar_split_clause,[],[f94,f74,f65,f60,f114])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl5_4 <=> r1_lattice3(sK0,k1_xboole_0,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.53  fof(f94,plain,(
% 0.22/0.53    m1_subset_1(sK2(sK0,k1_xboole_0,sK1),u1_struct_0(sK0)) | (~spl5_1 | ~spl5_2 | spl5_4)),
% 0.22/0.53    inference(unit_resulting_resolution,[],[f62,f67,f76,f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f24,f25])).
% 0.22/0.53  % (7237)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (7216)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X2,X4) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(rectify,[],[f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (((r1_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X2,X3) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r1_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(flattening,[],[f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : ((r1_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X2,X3) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X2,X3))))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattice3)).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    ~r1_lattice3(sK0,k1_xboole_0,sK1) | spl5_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f74])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    ~spl5_7 | ~spl5_1 | ~spl5_2 | spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f93,f74,f65,f60,f109])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ~r1_orders_2(sK0,sK1,sK2(sK0,k1_xboole_0,sK1)) | (~spl5_1 | ~spl5_2 | spl5_4)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f62,f67,f76,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X2,sK2(X0,X1,X2)) | r1_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f103,plain,(
% 0.22/0.54    spl5_6 | ~spl5_1 | ~spl5_2 | spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f95,f74,f65,f60,f100])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    r2_hidden(sK2(sK0,k1_xboole_0,sK1),k1_xboole_0) | (~spl5_1 | ~spl5_2 | spl5_4)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f62,f67,f76,f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK2(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattice3(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f92,plain,(
% 0.22/0.54    spl5_5 | ~spl5_1 | ~spl5_2 | spl5_3),
% 0.22/0.54    inference(avatar_split_clause,[],[f85,f70,f65,f60,f89])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    r2_hidden(sK3(sK0,k1_xboole_0,sK1),k1_xboole_0) | (~spl5_1 | ~spl5_2 | spl5_3)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f62,f72,f67,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_lattice3(X0,X1,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f30])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    ~spl5_3 | ~spl5_4),
% 0.22/0.54    inference(avatar_split_clause,[],[f37,f74,f70])).
% 0.22/0.54  fof(f37,plain,(
% 0.22/0.54    ~r1_lattice3(sK0,k1_xboole_0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ((~r1_lattice3(sK0,k1_xboole_0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f20,f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0)) => (? [X1] : ((~r1_lattice3(sK0,k1_xboole_0,X1) | ~r2_lattice3(sK0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ? [X1] : ((~r1_lattice3(sK0,k1_xboole_0,X1) | ~r2_lattice3(sK0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~r1_lattice3(sK0,k1_xboole_0,sK1) | ~r2_lattice3(sK0,k1_xboole_0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((~r1_lattice3(X0,k1_xboole_0,X1) | ~r2_lattice3(X0,k1_xboole_0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.22/0.54    inference(negated_conjecture,[],[f8])).
% 0.22/0.54  fof(f8,conjecture,(
% 0.22/0.54    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (r1_lattice3(X0,k1_xboole_0,X1) & r2_lattice3(X0,k1_xboole_0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_yellow_0)).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f36,f65])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f63,plain,(
% 0.22/0.54    spl5_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f35,f60])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    l1_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (7236)------------------------------
% 0.22/0.54  % (7236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7236)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (7236)Memory used [KB]: 10874
% 0.22/0.54  % (7236)Time elapsed: 0.062 s
% 0.22/0.54  % (7236)------------------------------
% 0.22/0.54  % (7236)------------------------------
% 0.22/0.54  % (7212)Success in time 0.176 s
%------------------------------------------------------------------------------
