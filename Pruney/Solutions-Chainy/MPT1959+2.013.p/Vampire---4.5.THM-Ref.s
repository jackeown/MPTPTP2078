%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 353 expanded)
%              Number of leaves         :   40 ( 139 expanded)
%              Depth                    :   12
%              Number of atoms          :  812 (2177 expanded)
%              Number of equality atoms :   49 (  79 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f654,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f111,f116,f121,f126,f136,f141,f151,f153,f176,f193,f317,f325,f337,f344,f361,f406,f519,f533,f545,f585,f603,f620,f652,f653])).

fof(f653,plain,
    ( u1_struct_0(sK0) != sK1
    | v1_subset_1(sK1,sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f652,plain,
    ( spl6_50
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f636,f173,f138,f600])).

fof(f600,plain,
    ( spl6_50
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f138,plain,
    ( spl6_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f173,plain,
    ( spl6_15
  <=> u1_struct_0(sK0) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f636,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_10
    | ~ spl6_15 ),
    inference(backward_demodulation,[],[f140,f175])).

fof(f175,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f173])).

fof(f140,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f620,plain,
    ( ~ spl6_49
    | ~ spl6_50 ),
    inference(avatar_contradiction_clause,[],[f609])).

fof(f609,plain,
    ( $false
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(unit_resulting_resolution,[],[f596,f602,f87])).

fof(f87,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ v1_subset_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f602,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f600])).

fof(f596,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl6_49
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f603,plain,
    ( spl6_50
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_45
    | spl6_48 ),
    inference(avatar_split_clause,[],[f554,f542,f517,f297,f138,f600])).

fof(f297,plain,
    ( spl6_27
  <=> r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f517,plain,
    ( spl6_45
  <=> ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK4(u1_struct_0(sK0),X0,sK1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f542,plain,
    ( spl6_48
  <=> r2_hidden(sK4(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f554,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_10
    | ~ spl6_27
    | ~ spl6_45
    | spl6_48 ),
    inference(backward_demodulation,[],[f140,f548])).

fof(f548,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl6_27
    | ~ spl6_45
    | spl6_48 ),
    inference(subsumption_resolution,[],[f547,f298])).

fof(f298,plain,
    ( r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f297])).

fof(f547,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = sK1
    | ~ spl6_45
    | spl6_48 ),
    inference(resolution,[],[f544,f518])).

fof(f518,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(u1_struct_0(sK0),X0,sK1),sK1)
        | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = X0 )
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f517])).

fof(f544,plain,
    ( ~ r2_hidden(sK4(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | spl6_48 ),
    inference(avatar_component_clause,[],[f542])).

fof(f585,plain,
    ( spl6_15
    | ~ spl6_27
    | ~ spl6_45
    | spl6_48 ),
    inference(avatar_split_clause,[],[f548,f542,f517,f297,f173])).

fof(f545,plain,
    ( ~ spl6_48
    | spl6_15
    | ~ spl6_17
    | ~ spl6_27
    | ~ spl6_47 ),
    inference(avatar_split_clause,[],[f540,f531,f297,f191,f173,f542])).

fof(f191,plain,
    ( spl6_17
  <=> ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | r2_hidden(X3,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f531,plain,
    ( spl6_47
  <=> ! [X7] :
        ( ~ r2_hidden(sK4(u1_struct_0(sK0),X7,sK1),X7)
        | sK1 = X7
        | ~ r2_hidden(X7,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).

fof(f540,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ r2_hidden(sK4(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | ~ spl6_17
    | ~ spl6_27
    | ~ spl6_47 ),
    inference(subsumption_resolution,[],[f537,f298])).

fof(f537,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK4(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)
    | ~ spl6_17
    | ~ spl6_47 ),
    inference(resolution,[],[f532,f192])).

fof(f192,plain,
    ( ! [X3] :
        ( r2_hidden(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f191])).

fof(f532,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK4(u1_struct_0(sK0),X7,sK1),X7)
        | sK1 = X7
        | ~ r2_hidden(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_47 ),
    inference(avatar_component_clause,[],[f531])).

fof(f533,plain,
    ( spl6_47
    | ~ spl6_10
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f529,f517,f138,f531])).

fof(f529,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK4(u1_struct_0(sK0),X7,sK1),X7)
        | sK1 = X7
        | ~ r2_hidden(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_10
    | ~ spl6_45 ),
    inference(subsumption_resolution,[],[f418,f518])).

fof(f418,plain,
    ( ! [X7] :
        ( ~ r2_hidden(sK4(u1_struct_0(sK0),X7,sK1),X7)
        | ~ r2_hidden(sK4(u1_struct_0(sK0),X7,sK1),sK1)
        | sK1 = X7
        | ~ r2_hidden(X7,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_10 ),
    inference(resolution,[],[f140,f220])).

fof(f220,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | X1 = X2
      | ~ r2_hidden(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f78,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ( ( ~ r2_hidden(sK4(X0,X1,X2),X2)
              | ~ r2_hidden(sK4(X0,X1,X2),X1) )
            & ( r2_hidden(sK4(X0,X1,X2),X2)
              | r2_hidden(sK4(X0,X1,X2),X1) )
            & m1_subset_1(sK4(X0,X1,X2),X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X2)
            | ~ r2_hidden(X3,X1) )
          & ( r2_hidden(X3,X2)
            | r2_hidden(X3,X1) )
          & m1_subset_1(X3,X0) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X2)
          | ~ r2_hidden(sK4(X0,X1,X2),X1) )
        & ( r2_hidden(sK4(X0,X1,X2),X2)
          | r2_hidden(sK4(X0,X1,X2),X1) )
        & m1_subset_1(sK4(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( ~ r2_hidden(X3,X2)
                | ~ r2_hidden(X3,X1) )
              & ( r2_hidden(X3,X2)
                | r2_hidden(X3,X1) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(f519,plain,
    ( spl6_45
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f480,f359,f335,f517])).

fof(f335,plain,
    ( spl6_33
  <=> ! [X3] :
        ( m1_subset_1(sK4(u1_struct_0(sK0),X3,sK1),u1_struct_0(sK0))
        | sK1 = X3
        | ~ r2_hidden(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f359,plain,
    ( spl6_35
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f480,plain,
    ( ! [X0] :
        ( sK1 = X0
        | ~ r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK4(u1_struct_0(sK0),X0,sK1),sK1) )
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(resolution,[],[f336,f360])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f359])).

fof(f336,plain,
    ( ! [X3] :
        ( m1_subset_1(sK4(u1_struct_0(sK0),X3,sK1),u1_struct_0(sK0))
        | sK1 = X3
        | ~ r2_hidden(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f335])).

fof(f406,plain,
    ( ~ spl6_6
    | spl6_7
    | spl6_12
    | ~ spl6_15 ),
    inference(avatar_contradiction_clause,[],[f405])).

fof(f405,plain,
    ( $false
    | ~ spl6_6
    | spl6_7
    | spl6_12
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f404,f120])).

fof(f120,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f404,plain,
    ( ~ l1_orders_2(sK0)
    | spl6_7
    | spl6_12
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f403,f125])).

fof(f125,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl6_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f403,plain,
    ( v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | spl6_12
    | ~ spl6_15 ),
    inference(subsumption_resolution,[],[f389,f150])).

fof(f150,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl6_12
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f389,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_xboole_0(sK1)
    | ~ l1_orders_2(sK0)
    | ~ spl6_15 ),
    inference(superposition,[],[f156,f175])).

fof(f156,plain,(
    ! [X2] :
      ( r2_hidden(k3_yellow_0(X2),u1_struct_0(X2))
      | v1_xboole_0(u1_struct_0(X2))
      | ~ l1_orders_2(X2) ) ),
    inference(resolution,[],[f72,f63])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f361,plain,
    ( spl6_35
    | spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f354,f342,f148,f118,f113,f108,f93,f359])).

fof(f93,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f108,plain,
    ( spl6_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f113,plain,
    ( spl6_5
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f342,plain,
    ( spl6_34
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f354,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1) )
    | spl6_1
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f353,f95])).

fof(f95,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f353,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | v2_struct_0(sK0) )
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f352,f110])).

fof(f110,plain,
    ( v5_orders_2(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f352,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f351,f115])).

fof(f115,plain,
    ( v1_yellow_0(sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f351,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_6
    | ~ spl6_12
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f350,f120])).

fof(f350,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,sK1)
        | ~ l1_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_12
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f349,f149])).

fof(f149,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f148])).

fof(f349,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1)
        | ~ l1_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_34 ),
    inference(duplicate_literal_removal,[],[f347])).

fof(f347,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_34 ),
    inference(resolution,[],[f343,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f343,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | r2_hidden(X1,sK1) )
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f342])).

fof(f344,plain,
    ( spl6_34
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f340,f323,f138,f133,f342])).

fof(f133,plain,
    ( spl6_9
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f323,plain,
    ( spl6_32
  <=> ! [X1,X0,X2] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f340,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1) )
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_32 ),
    inference(subsumption_resolution,[],[f338,f140])).

fof(f338,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,sK1) )
    | ~ spl6_9
    | ~ spl6_32 ),
    inference(resolution,[],[f324,f135])).

fof(f135,plain,
    ( v13_waybel_0(sK1,sK0)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f133])).

fof(f324,plain,
    ( ! [X2,X0,X1] :
        ( ~ v13_waybel_0(X2,sK0)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f323])).

fof(f337,plain,
    ( spl6_33
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f280,f138,f335])).

fof(f280,plain,
    ( ! [X3] :
        ( m1_subset_1(sK4(u1_struct_0(sK0),X3,sK1),u1_struct_0(sK0))
        | sK1 = X3
        | ~ r2_hidden(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_10 ),
    inference(resolution,[],[f212,f140])).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | X1 = X2
      | ~ r2_hidden(X1,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f76,f71])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f325,plain,
    ( spl6_32
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f229,f118,f323])).

fof(f229,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,X2)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_waybel_0(X2,sK0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X1,X2) )
    | ~ spl6_6 ),
    inference(resolution,[],[f225,f120])).

fof(f225,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X5,X1) ) ),
    inference(subsumption_resolution,[],[f64,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f64,plain,(
    ! [X4,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r1_orders_2(X0,X4,X5)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ v13_waybel_0(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ( ~ r2_hidden(sK3(X0,X1),X1)
                & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
                & r2_hidden(sK2(X0,X1),X1)
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ? [X3] :
              ( ~ r2_hidden(X3,X1)
              & r1_orders_2(X0,X2,X3)
              & r2_hidden(X2,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ? [X3] :
            ( ~ r2_hidden(X3,X1)
            & r1_orders_2(X0,sK2(X0,X1),X3)
            & r2_hidden(sK2(X0,X1),X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,X1)
          & r1_orders_2(X0,sK2(X0,X1),X3)
          & r2_hidden(sK2(X0,X1),X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1))
        & r2_hidden(sK2(X0,X1),X1)
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( ! [X5] :
                      ( r2_hidden(X5,X1)
                      | ~ r1_orders_2(X0,X4,X5)
                      | ~ r2_hidden(X4,X1)
                      | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v13_waybel_0(X1,X0)
              | ? [X2] :
                  ( ? [X3] :
                      ( ~ r2_hidden(X3,X1)
                      & r1_orders_2(X0,X2,X3)
                      & r2_hidden(X2,X1)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ! [X3] :
                      ( r2_hidden(X3,X1)
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r2_hidden(X2,X1)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ v13_waybel_0(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f317,plain,(
    spl6_27 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl6_27 ),
    inference(subsumption_resolution,[],[f314,f88])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f314,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0))
    | spl6_27 ),
    inference(resolution,[],[f299,f90])).

fof(f90,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK5(X0,X1),X0)
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( r1_tarski(sK5(X0,X1),X0)
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK5(X0,X1),X0)
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( r1_tarski(sK5(X0,X1),X0)
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f299,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f297])).

fof(f193,plain,
    ( spl6_17
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f186,f138,f191])).

fof(f186,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | r2_hidden(X3,u1_struct_0(sK0)) )
    | ~ spl6_10 ),
    inference(resolution,[],[f75,f140])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f176,plain,
    ( spl6_15
    | ~ spl6_10
    | spl6_11 ),
    inference(avatar_split_clause,[],[f169,f144,f138,f173])).

fof(f144,plain,
    ( spl6_11
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f169,plain,
    ( u1_struct_0(sK0) = sK1
    | ~ spl6_10
    | spl6_11 ),
    inference(subsumption_resolution,[],[f167,f145])).

fof(f145,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f144])).

fof(f167,plain,
    ( u1_struct_0(sK0) = sK1
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(resolution,[],[f74,f140])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f153,plain,
    ( ~ spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f152,f148,f144])).

fof(f152,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_12 ),
    inference(subsumption_resolution,[],[f62,f150])).

fof(f62,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( r2_hidden(k3_yellow_0(sK0),sK1)
      | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
    & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
      | v1_subset_1(sK1,u1_struct_0(sK0)) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v13_waybel_0(sK1,sK0)
    & v2_waybel_0(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l1_orders_2(sK0)
    & v1_yellow_0(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( r2_hidden(k3_yellow_0(X0),X1)
              | ~ v1_subset_1(X1,u1_struct_0(X0)) )
            & ( ~ r2_hidden(k3_yellow_0(X0),X1)
              | v1_subset_1(X1,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(sK0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
          & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
            | v1_subset_1(X1,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v13_waybel_0(X1,sK0)
          & v2_waybel_0(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(sK0)
      & v1_yellow_0(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( r2_hidden(k3_yellow_0(sK0),X1)
          | ~ v1_subset_1(X1,u1_struct_0(sK0)) )
        & ( ~ r2_hidden(k3_yellow_0(sK0),X1)
          | v1_subset_1(X1,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v13_waybel_0(X1,sK0)
        & v2_waybel_0(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ( r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ v1_subset_1(sK1,u1_struct_0(sK0)) )
      & ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | v1_subset_1(sK1,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v13_waybel_0(sK1,sK0)
      & v2_waybel_0(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(k3_yellow_0(X0),X1)
            | ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & ( ~ r2_hidden(k3_yellow_0(X0),X1)
            | v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f151,plain,
    ( spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f61,f148,f144])).

fof(f61,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f34])).

fof(f141,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f60,f138])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f136,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f59,f133])).

fof(f59,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f126,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f57,f123])).

fof(f57,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f121,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f56,f118])).

fof(f56,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f116,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f55,f113])).

% (5968)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f55,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f111,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f54,f108])).

fof(f54,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f51,f93])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (5981)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.46  % (5973)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.48  % (5974)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (5983)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  % (5967)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.49  % (5967)Refutation not found, incomplete strategy% (5967)------------------------------
% 0.20/0.49  % (5967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5967)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (5967)Memory used [KB]: 6140
% 0.20/0.49  % (5967)Time elapsed: 0.098 s
% 0.20/0.49  % (5967)------------------------------
% 0.20/0.49  % (5967)------------------------------
% 0.20/0.50  % (5972)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (5982)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.50  % (5975)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (5964)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (5984)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (5962)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.50  % (5966)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (5962)Refutation not found, incomplete strategy% (5962)------------------------------
% 0.20/0.50  % (5962)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (5962)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (5962)Memory used [KB]: 10618
% 0.20/0.50  % (5962)Time elapsed: 0.104 s
% 0.20/0.50  % (5962)------------------------------
% 0.20/0.50  % (5962)------------------------------
% 0.20/0.50  % (5965)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (5980)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (5963)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (5969)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (5969)Refutation not found, incomplete strategy% (5969)------------------------------
% 0.20/0.51  % (5969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (5969)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (5969)Memory used [KB]: 1663
% 0.20/0.51  % (5969)Time elapsed: 0.113 s
% 0.20/0.51  % (5969)------------------------------
% 0.20/0.51  % (5969)------------------------------
% 0.20/0.51  % (5985)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (5976)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (5977)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (5964)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f654,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f96,f111,f116,f121,f126,f136,f141,f151,f153,f176,f193,f317,f325,f337,f344,f361,f406,f519,f533,f545,f585,f603,f620,f652,f653])).
% 0.20/0.52  fof(f653,plain,(
% 0.20/0.52    u1_struct_0(sK0) != sK1 | v1_subset_1(sK1,sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f652,plain,(
% 0.20/0.52    spl6_50 | ~spl6_10 | ~spl6_15),
% 0.20/0.52    inference(avatar_split_clause,[],[f636,f173,f138,f600])).
% 0.20/0.52  fof(f600,plain,(
% 0.20/0.52    spl6_50 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    spl6_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    spl6_15 <=> u1_struct_0(sK0) = sK1),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.52  fof(f636,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl6_10 | ~spl6_15)),
% 0.20/0.52    inference(backward_demodulation,[],[f140,f175])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    u1_struct_0(sK0) = sK1 | ~spl6_15),
% 0.20/0.52    inference(avatar_component_clause,[],[f173])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f138])).
% 0.20/0.52  fof(f620,plain,(
% 0.20/0.52    ~spl6_49 | ~spl6_50),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f609])).
% 0.20/0.52  fof(f609,plain,(
% 0.20/0.52    $false | (~spl6_49 | ~spl6_50)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f596,f602,f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f73])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0,X1] : (X0 != X1 | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.52  fof(f602,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl6_50),
% 0.20/0.52    inference(avatar_component_clause,[],[f600])).
% 0.20/0.52  fof(f596,plain,(
% 0.20/0.52    v1_subset_1(sK1,sK1) | ~spl6_49),
% 0.20/0.52    inference(avatar_component_clause,[],[f594])).
% 0.20/0.52  fof(f594,plain,(
% 0.20/0.52    spl6_49 <=> v1_subset_1(sK1,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).
% 0.20/0.52  fof(f603,plain,(
% 0.20/0.52    spl6_50 | ~spl6_10 | ~spl6_27 | ~spl6_45 | spl6_48),
% 0.20/0.52    inference(avatar_split_clause,[],[f554,f542,f517,f297,f138,f600])).
% 0.20/0.52  fof(f297,plain,(
% 0.20/0.52    spl6_27 <=> r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.52  fof(f517,plain,(
% 0.20/0.52    spl6_45 <=> ! [X0] : (sK1 = X0 | ~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),X0,sK1),sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.20/0.52  fof(f542,plain,(
% 0.20/0.52    spl6_48 <=> r2_hidden(sK4(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.20/0.52  fof(f554,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl6_10 | ~spl6_27 | ~spl6_45 | spl6_48)),
% 0.20/0.52    inference(backward_demodulation,[],[f140,f548])).
% 0.20/0.52  fof(f548,plain,(
% 0.20/0.52    u1_struct_0(sK0) = sK1 | (~spl6_27 | ~spl6_45 | spl6_48)),
% 0.20/0.52    inference(subsumption_resolution,[],[f547,f298])).
% 0.20/0.52  fof(f298,plain,(
% 0.20/0.52    r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_27),
% 0.20/0.52    inference(avatar_component_clause,[],[f297])).
% 0.20/0.52  fof(f547,plain,(
% 0.20/0.52    ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = sK1 | (~spl6_45 | spl6_48)),
% 0.20/0.52    inference(resolution,[],[f544,f518])).
% 0.20/0.52  fof(f518,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK4(u1_struct_0(sK0),X0,sK1),sK1) | ~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = X0) ) | ~spl6_45),
% 0.20/0.52    inference(avatar_component_clause,[],[f517])).
% 0.20/0.52  fof(f544,plain,(
% 0.20/0.52    ~r2_hidden(sK4(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | spl6_48),
% 0.20/0.52    inference(avatar_component_clause,[],[f542])).
% 0.20/0.52  fof(f585,plain,(
% 0.20/0.52    spl6_15 | ~spl6_27 | ~spl6_45 | spl6_48),
% 0.20/0.52    inference(avatar_split_clause,[],[f548,f542,f517,f297,f173])).
% 0.20/0.52  fof(f545,plain,(
% 0.20/0.52    ~spl6_48 | spl6_15 | ~spl6_17 | ~spl6_27 | ~spl6_47),
% 0.20/0.52    inference(avatar_split_clause,[],[f540,f531,f297,f191,f173,f542])).
% 0.20/0.52  fof(f191,plain,(
% 0.20/0.52    spl6_17 <=> ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(X3,u1_struct_0(sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.52  fof(f531,plain,(
% 0.20/0.52    spl6_47 <=> ! [X7] : (~r2_hidden(sK4(u1_struct_0(sK0),X7,sK1),X7) | sK1 = X7 | ~r2_hidden(X7,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_47])])).
% 0.20/0.52  fof(f540,plain,(
% 0.20/0.52    u1_struct_0(sK0) = sK1 | ~r2_hidden(sK4(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | (~spl6_17 | ~spl6_27 | ~spl6_47)),
% 0.20/0.52    inference(subsumption_resolution,[],[f537,f298])).
% 0.20/0.52  fof(f537,plain,(
% 0.20/0.52    u1_struct_0(sK0) = sK1 | ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(u1_struct_0(sK0),u1_struct_0(sK0),sK1),sK1) | (~spl6_17 | ~spl6_47)),
% 0.20/0.52    inference(resolution,[],[f532,f192])).
% 0.20/0.52  fof(f192,plain,(
% 0.20/0.52    ( ! [X3] : (r2_hidden(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1)) ) | ~spl6_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f191])).
% 0.20/0.52  fof(f532,plain,(
% 0.20/0.52    ( ! [X7] : (~r2_hidden(sK4(u1_struct_0(sK0),X7,sK1),X7) | sK1 = X7 | ~r2_hidden(X7,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_47),
% 0.20/0.52    inference(avatar_component_clause,[],[f531])).
% 0.20/0.52  fof(f533,plain,(
% 0.20/0.52    spl6_47 | ~spl6_10 | ~spl6_45),
% 0.20/0.52    inference(avatar_split_clause,[],[f529,f517,f138,f531])).
% 0.20/0.52  fof(f529,plain,(
% 0.20/0.52    ( ! [X7] : (~r2_hidden(sK4(u1_struct_0(sK0),X7,sK1),X7) | sK1 = X7 | ~r2_hidden(X7,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl6_10 | ~spl6_45)),
% 0.20/0.52    inference(subsumption_resolution,[],[f418,f518])).
% 0.20/0.52  fof(f418,plain,(
% 0.20/0.52    ( ! [X7] : (~r2_hidden(sK4(u1_struct_0(sK0),X7,sK1),X7) | ~r2_hidden(sK4(u1_struct_0(sK0),X7,sK1),sK1) | sK1 = X7 | ~r2_hidden(X7,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_10),
% 0.20/0.52    inference(resolution,[],[f140,f220])).
% 0.20/0.52  fof(f220,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | X1 = X2 | ~r2_hidden(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(resolution,[],[f78,f71])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ((~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1)) & (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1)) & m1_subset_1(sK4(X0,X1,X2),X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f42,f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) => ((~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1)) & (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1)) & m1_subset_1(sK4(X0,X1,X2),X0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(flattening,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : (((~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & (r2_hidden(X3,X2) | r2_hidden(X3,X1))) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(flattening,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).
% 0.20/0.52  fof(f519,plain,(
% 0.20/0.52    spl6_45 | ~spl6_33 | ~spl6_35),
% 0.20/0.52    inference(avatar_split_clause,[],[f480,f359,f335,f517])).
% 0.20/0.52  fof(f335,plain,(
% 0.20/0.52    spl6_33 <=> ! [X3] : (m1_subset_1(sK4(u1_struct_0(sK0),X3,sK1),u1_struct_0(sK0)) | sK1 = X3 | ~r2_hidden(X3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.20/0.52  fof(f359,plain,(
% 0.20/0.52    spl6_35 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.20/0.52  fof(f480,plain,(
% 0.20/0.52    ( ! [X0] : (sK1 = X0 | ~r2_hidden(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),X0,sK1),sK1)) ) | (~spl6_33 | ~spl6_35)),
% 0.20/0.52    inference(resolution,[],[f336,f360])).
% 0.20/0.52  fof(f360,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | ~spl6_35),
% 0.20/0.52    inference(avatar_component_clause,[],[f359])).
% 0.20/0.52  fof(f336,plain,(
% 0.20/0.52    ( ! [X3] : (m1_subset_1(sK4(u1_struct_0(sK0),X3,sK1),u1_struct_0(sK0)) | sK1 = X3 | ~r2_hidden(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_33),
% 0.20/0.52    inference(avatar_component_clause,[],[f335])).
% 0.20/0.52  fof(f406,plain,(
% 0.20/0.52    ~spl6_6 | spl6_7 | spl6_12 | ~spl6_15),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f405])).
% 0.20/0.52  fof(f405,plain,(
% 0.20/0.52    $false | (~spl6_6 | spl6_7 | spl6_12 | ~spl6_15)),
% 0.20/0.52    inference(subsumption_resolution,[],[f404,f120])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    l1_orders_2(sK0) | ~spl6_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f118])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    spl6_6 <=> l1_orders_2(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.52  fof(f404,plain,(
% 0.20/0.52    ~l1_orders_2(sK0) | (spl6_7 | spl6_12 | ~spl6_15)),
% 0.20/0.52    inference(subsumption_resolution,[],[f403,f125])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    ~v1_xboole_0(sK1) | spl6_7),
% 0.20/0.52    inference(avatar_component_clause,[],[f123])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    spl6_7 <=> v1_xboole_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.52  fof(f403,plain,(
% 0.20/0.52    v1_xboole_0(sK1) | ~l1_orders_2(sK0) | (spl6_12 | ~spl6_15)),
% 0.20/0.52    inference(subsumption_resolution,[],[f389,f150])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    ~r2_hidden(k3_yellow_0(sK0),sK1) | spl6_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f148])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    spl6_12 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.52  fof(f389,plain,(
% 0.20/0.52    r2_hidden(k3_yellow_0(sK0),sK1) | v1_xboole_0(sK1) | ~l1_orders_2(sK0) | ~spl6_15),
% 0.20/0.52    inference(superposition,[],[f156,f175])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    ( ! [X2] : (r2_hidden(k3_yellow_0(X2),u1_struct_0(X2)) | v1_xboole_0(u1_struct_0(X2)) | ~l1_orders_2(X2)) )),
% 0.20/0.52    inference(resolution,[],[f72,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.52  fof(f361,plain,(
% 0.20/0.52    spl6_35 | spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_34),
% 0.20/0.52    inference(avatar_split_clause,[],[f354,f342,f148,f118,f113,f108,f93,f359])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    spl6_1 <=> v2_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    spl6_4 <=> v5_orders_2(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    spl6_5 <=> v1_yellow_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.52  fof(f342,plain,(
% 0.20/0.52    spl6_34 <=> ! [X1,X0] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.20/0.52  fof(f354,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1)) ) | (spl6_1 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_34)),
% 0.20/0.52    inference(subsumption_resolution,[],[f353,f95])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ~v2_struct_0(sK0) | spl6_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f93])).
% 0.20/0.52  fof(f353,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | v2_struct_0(sK0)) ) | (~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_34)),
% 0.20/0.52    inference(subsumption_resolution,[],[f352,f110])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    v5_orders_2(sK0) | ~spl6_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f108])).
% 0.20/0.52  fof(f352,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_5 | ~spl6_6 | ~spl6_12 | ~spl6_34)),
% 0.20/0.52    inference(subsumption_resolution,[],[f351,f115])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    v1_yellow_0(sK0) | ~spl6_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f113])).
% 0.20/0.52  fof(f351,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_6 | ~spl6_12 | ~spl6_34)),
% 0.20/0.52    inference(subsumption_resolution,[],[f350,f120])).
% 0.20/0.52  fof(f350,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,sK1) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | (~spl6_12 | ~spl6_34)),
% 0.20/0.52    inference(subsumption_resolution,[],[f349,f149])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    r2_hidden(k3_yellow_0(sK0),sK1) | ~spl6_12),
% 0.20/0.52    inference(avatar_component_clause,[],[f148])).
% 0.20/0.52  fof(f349,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_34),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f347])).
% 0.20/0.52  fof(f347,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v1_yellow_0(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_34),
% 0.20/0.52    inference(resolution,[],[f343,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).
% 0.20/0.52  fof(f343,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | r2_hidden(X1,sK1)) ) | ~spl6_34),
% 0.20/0.52    inference(avatar_component_clause,[],[f342])).
% 0.20/0.52  fof(f344,plain,(
% 0.20/0.52    spl6_34 | ~spl6_9 | ~spl6_10 | ~spl6_32),
% 0.20/0.52    inference(avatar_split_clause,[],[f340,f323,f138,f133,f342])).
% 0.20/0.52  fof(f133,plain,(
% 0.20/0.52    spl6_9 <=> v13_waybel_0(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.52  fof(f323,plain,(
% 0.20/0.52    spl6_32 <=> ! [X1,X0,X2] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.20/0.52  fof(f340,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1)) ) | (~spl6_9 | ~spl6_10 | ~spl6_32)),
% 0.20/0.52    inference(subsumption_resolution,[],[f338,f140])).
% 0.20/0.52  fof(f338,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,sK1)) ) | (~spl6_9 | ~spl6_32)),
% 0.20/0.52    inference(resolution,[],[f324,f135])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    v13_waybel_0(sK1,sK0) | ~spl6_9),
% 0.20/0.52    inference(avatar_component_clause,[],[f133])).
% 0.20/0.52  fof(f324,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v13_waybel_0(X2,sK0) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl6_32),
% 0.20/0.52    inference(avatar_component_clause,[],[f323])).
% 0.20/0.52  fof(f337,plain,(
% 0.20/0.52    spl6_33 | ~spl6_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f280,f138,f335])).
% 0.20/0.52  fof(f280,plain,(
% 0.20/0.52    ( ! [X3] : (m1_subset_1(sK4(u1_struct_0(sK0),X3,sK1),u1_struct_0(sK0)) | sK1 = X3 | ~r2_hidden(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_10),
% 0.20/0.52    inference(resolution,[],[f212,f140])).
% 0.20/0.52  fof(f212,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK4(X0,X1,X2),X0) | X1 = X2 | ~r2_hidden(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.52    inference(resolution,[],[f76,f71])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(sK4(X0,X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | X1 = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f44])).
% 0.20/0.52  fof(f325,plain,(
% 0.20/0.52    spl6_32 | ~spl6_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f229,f118,f323])).
% 0.20/0.52  fof(f229,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_waybel_0(X2,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,X2)) ) | ~spl6_6),
% 0.20/0.52    inference(resolution,[],[f225,f120])).
% 0.20/0.52  fof(f225,plain,(
% 0.20/0.52    ( ! [X4,X0,X5,X1] : (~l1_orders_2(X0) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X5,X1)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f64,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.52    inference(flattening,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X4,X0,X5,X1] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0)) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~v13_waybel_0(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ((~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f36,f38,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) => (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,sK2(X0,X1),X3) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r2_hidden(sK3(X0,X1),X1) & r1_orders_2(X0,sK2(X0,X1),sK3(X0,X1)) & r2_hidden(sK2(X0,X1),X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X4] : (! [X5] : (r2_hidden(X5,X1) | ~r1_orders_2(X0,X4,X5) | ~r2_hidden(X4,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(rectify,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (((v13_waybel_0(X1,X0) | ? [X2] : (? [X3] : (~r2_hidden(X3,X1) & r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~v13_waybel_0(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 0.20/0.52  fof(f317,plain,(
% 0.20/0.52    spl6_27),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f316])).
% 0.20/0.52  fof(f316,plain,(
% 0.20/0.52    $false | spl6_27),
% 0.20/0.52    inference(subsumption_resolution,[],[f314,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f80])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(flattening,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f314,plain,(
% 0.20/0.52    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK0)) | spl6_27),
% 0.20/0.52    inference(resolution,[],[f299,f90])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f83])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f48,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK5(X0,X1),X0) | ~r2_hidden(sK5(X0,X1),X1)) & (r1_tarski(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.52    inference(rectify,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.20/0.52  fof(f299,plain,(
% 0.20/0.52    ~r2_hidden(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_27),
% 0.20/0.52    inference(avatar_component_clause,[],[f297])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    spl6_17 | ~spl6_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f186,f138,f191])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    ( ! [X3] : (~r2_hidden(X3,sK1) | r2_hidden(X3,u1_struct_0(sK0))) ) | ~spl6_10),
% 0.20/0.52    inference(resolution,[],[f75,f140])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    spl6_15 | ~spl6_10 | spl6_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f169,f144,f138,f173])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    spl6_11 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.52  fof(f169,plain,(
% 0.20/0.52    u1_struct_0(sK0) = sK1 | (~spl6_10 | spl6_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f167,f145])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl6_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f144])).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    u1_struct_0(sK0) = sK1 | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_10),
% 0.20/0.52    inference(resolution,[],[f74,f140])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f40])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    ~spl6_11 | spl6_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f152,f148,f144])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    ~v1_subset_1(sK1,u1_struct_0(sK0)) | spl6_12),
% 0.20/0.52    inference(subsumption_resolution,[],[f62,f150])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) & l1_orders_2(sK0) & v1_yellow_0(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ? [X1] : ((r2_hidden(k3_yellow_0(sK0),X1) | ~v1_subset_1(X1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),X1) | v1_subset_1(X1,u1_struct_0(sK0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(X1,sK0) & v2_waybel_0(X1,sK0) & ~v1_xboole_0(X1)) => ((r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))) & (~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & v13_waybel_0(sK1,sK0) & v2_waybel_0(sK1,sK0) & ~v1_xboole_0(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (((r2_hidden(k3_yellow_0(X0),X1) | ~v1_subset_1(X1,u1_struct_0(X0))) & (~r2_hidden(k3_yellow_0(X0),X1) | v1_subset_1(X1,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.52    inference(negated_conjecture,[],[f12])).
% 0.20/0.52  fof(f12,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    spl6_11 | ~spl6_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f61,f148,f144])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    spl6_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f60,f138])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    spl6_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f59,f133])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    v13_waybel_0(sK1,sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    ~spl6_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f57,f123])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ~v1_xboole_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    spl6_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f56,f118])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    l1_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    spl6_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f55,f113])).
% 0.20/0.52  % (5968)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    v1_yellow_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    spl6_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f54,f108])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    v5_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ~spl6_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f51,f93])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (5964)------------------------------
% 0.20/0.52  % (5964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (5964)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (5964)Memory used [KB]: 6524
% 0.20/0.52  % (5964)Time elapsed: 0.110 s
% 0.20/0.52  % (5964)------------------------------
% 0.20/0.52  % (5964)------------------------------
% 0.20/0.52  % (5961)Success in time 0.169 s
%------------------------------------------------------------------------------
