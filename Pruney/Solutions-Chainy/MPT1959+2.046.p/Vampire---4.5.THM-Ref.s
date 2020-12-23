%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:57 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 256 expanded)
%              Number of leaves         :   32 (  93 expanded)
%              Depth                    :    9
%              Number of atoms          :  409 (1165 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f413,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f90,f95,f100,f109,f110,f116,f143,f158,f166,f241,f259,f266,f287,f293,f295,f317,f323,f353,f412])).

fof(f412,plain,(
    ~ spl6_27 ),
    inference(avatar_contradiction_clause,[],[f411])).

fof(f411,plain,
    ( $false
    | ~ spl6_27 ),
    inference(resolution,[],[f352,f176])).

fof(f176,plain,(
    ! [X4] : ~ v1_subset_1(X4,X4) ),
    inference(resolution,[],[f152,f65])).

fof(f65,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f152,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f148,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f148,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f61,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f352,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f350])).

fof(f350,plain,
    ( spl6_27
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f353,plain,
    ( spl6_27
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f325,f155,f102,f350])).

fof(f102,plain,
    ( spl6_8
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f155,plain,
    ( spl6_16
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f325,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ spl6_8
    | ~ spl6_16 ),
    inference(backward_demodulation,[],[f103,f157])).

fof(f157,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f155])).

fof(f103,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f323,plain,
    ( sK1 != u1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f317,plain,
    ( spl6_23
    | ~ spl6_5
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f313,f280,f87,f268])).

fof(f268,plain,
    ( spl6_23
  <=> r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f87,plain,
    ( spl6_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f280,plain,
    ( spl6_24
  <=> r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f313,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_5
    | ~ spl6_24 ),
    inference(resolution,[],[f281,f167])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | r2_hidden(X0,u1_struct_0(sK0)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f55,f89])).

fof(f89,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f281,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f280])).

fof(f295,plain,(
    spl6_25 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | spl6_25 ),
    inference(resolution,[],[f286,f152])).

fof(f286,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl6_25
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f293,plain,
    ( ~ spl6_21
    | ~ spl6_9
    | ~ spl6_10
    | spl6_24
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f292,f263,f239,f280,f113,f106,f256])).

fof(f256,plain,
    ( spl6_21
  <=> m1_subset_1(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f106,plain,
    ( spl6_9
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f113,plain,
    ( spl6_10
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f239,plain,
    ( spl6_20
  <=> ! [X3,X4] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r2_hidden(X4,sK1)
        | ~ r1_orders_2(sK0,X3,X4)
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f263,plain,
    ( spl6_22
  <=> r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f292,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ m1_subset_1(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_20
    | ~ spl6_22 ),
    inference(resolution,[],[f265,f240])).

fof(f240,plain,
    ( ! [X4,X3] :
        ( ~ r1_orders_2(sK0,X3,X4)
        | r2_hidden(X4,sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f239])).

fof(f265,plain,
    ( r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f263])).

fof(f287,plain,
    ( spl6_16
    | ~ spl6_24
    | ~ spl6_5
    | ~ spl6_25
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f275,f268,f284,f87,f280,f155])).

fof(f275,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)
    | sK1 = u1_struct_0(sK0)
    | ~ spl6_23 ),
    inference(resolution,[],[f270,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f270,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f268])).

fof(f266,plain,
    ( spl6_22
    | spl6_4
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f260,f256,f77,f72,f67,f82,f263])).

fof(f82,plain,
    ( spl6_4
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f67,plain,
    ( spl6_1
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f72,plain,
    ( spl6_2
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f77,plain,
    ( spl6_3
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f260,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v1_yellow_0(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))
    | ~ spl6_21 ),
    inference(resolution,[],[f258,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r1_orders_2(X0,k3_yellow_0(X0),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f258,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f256])).

fof(f259,plain,
    ( spl6_16
    | spl6_21
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f252,f87,f256,f155])).

fof(f252,plain,
    ( m1_subset_1(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f212,f152])).

fof(f212,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK4(u1_struct_0(sK0),sK1,X2),u1_struct_0(sK0))
        | sK1 = X2 )
    | ~ spl6_5 ),
    inference(resolution,[],[f58,f89])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(sK4(X0,X1,X2),X0)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f241,plain,
    ( ~ spl6_6
    | spl6_20
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f236,f87,f67,f239,f92])).

fof(f92,plain,
    ( spl6_6
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f236,plain,
    ( ! [X4,X3] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1)
        | ~ r1_orders_2(sK0,X3,X4)
        | r2_hidden(X4,sK1)
        | ~ v13_waybel_0(sK1,sK0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f48,f89])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f166,plain,
    ( sK1 != u1_struct_0(sK0)
    | r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f158,plain,
    ( spl6_8
    | spl6_16
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f153,f87,f155,f102])).

fof(f153,plain,
    ( sK1 = u1_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_5 ),
    inference(resolution,[],[f53,f89])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f143,plain,
    ( spl6_14
    | spl6_15
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f125,f113,f140,f136])).

fof(f136,plain,
    ( spl6_14
  <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f140,plain,
    ( spl6_15
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f125,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(resolution,[],[f52,f115])).

fof(f115,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f113])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f116,plain,
    ( spl6_10
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f111,f67,f113])).

fof(f111,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl6_1 ),
    inference(resolution,[],[f43,f69])).

fof(f69,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f67])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f110,plain,
    ( spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f34,f106,f102])).

fof(f34,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
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
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

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

fof(f109,plain,
    ( ~ spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f35,f106,f102])).

fof(f35,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f100,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f36,f97])).

fof(f97,plain,
    ( spl6_7
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f36,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f95,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f37,f92])).

fof(f37,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f38,f87])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f85,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f39,f82])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f80,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f40,f77])).

fof(f40,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f75,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f41,f72])).

fof(f41,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f42,f67])).

fof(f42,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:32:32 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.30/0.54  % (28478)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.30/0.56  % (28501)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.30/0.56  % (28482)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.55/0.56  % (28493)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.55/0.56  % (28494)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.55/0.57  % (28485)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.55/0.57  % (28483)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.55/0.57  % (28484)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.55/0.58  % (28480)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.55/0.58  % (28494)Refutation found. Thanks to Tanya!
% 1.55/0.58  % SZS status Theorem for theBenchmark
% 1.55/0.58  % SZS output start Proof for theBenchmark
% 1.55/0.58  fof(f413,plain,(
% 1.55/0.58    $false),
% 1.55/0.58    inference(avatar_sat_refutation,[],[f70,f75,f80,f85,f90,f95,f100,f109,f110,f116,f143,f158,f166,f241,f259,f266,f287,f293,f295,f317,f323,f353,f412])).
% 1.55/0.58  fof(f412,plain,(
% 1.55/0.58    ~spl6_27),
% 1.55/0.58    inference(avatar_contradiction_clause,[],[f411])).
% 1.55/0.58  fof(f411,plain,(
% 1.55/0.58    $false | ~spl6_27),
% 1.55/0.58    inference(resolution,[],[f352,f176])).
% 1.55/0.58  fof(f176,plain,(
% 1.55/0.58    ( ! [X4] : (~v1_subset_1(X4,X4)) )),
% 1.55/0.58    inference(resolution,[],[f152,f65])).
% 1.55/0.58  fof(f65,plain,(
% 1.55/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.55/0.58    inference(equality_resolution,[],[f54])).
% 1.55/0.58  fof(f54,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f27])).
% 1.55/0.58  fof(f27,plain,(
% 1.55/0.58    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f11])).
% 1.55/0.58  fof(f11,axiom,(
% 1.55/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.55/0.58  fof(f152,plain,(
% 1.55/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.55/0.58    inference(resolution,[],[f148,f62])).
% 1.55/0.58  fof(f62,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f6])).
% 1.55/0.58  fof(f6,axiom,(
% 1.55/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.55/0.58  fof(f148,plain,(
% 1.55/0.58    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 1.55/0.58    inference(duplicate_literal_removal,[],[f147])).
% 1.55/0.58  fof(f147,plain,(
% 1.55/0.58    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 1.55/0.58    inference(resolution,[],[f61,f60])).
% 1.55/0.58  fof(f60,plain,(
% 1.55/0.58    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f31])).
% 1.55/0.58  fof(f31,plain,(
% 1.55/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f1])).
% 1.55/0.58  fof(f1,axiom,(
% 1.55/0.58    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.55/0.58  fof(f61,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f31])).
% 1.55/0.58  fof(f352,plain,(
% 1.55/0.58    v1_subset_1(sK1,sK1) | ~spl6_27),
% 1.55/0.58    inference(avatar_component_clause,[],[f350])).
% 1.55/0.58  fof(f350,plain,(
% 1.55/0.58    spl6_27 <=> v1_subset_1(sK1,sK1)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 1.55/0.58  fof(f353,plain,(
% 1.55/0.58    spl6_27 | ~spl6_8 | ~spl6_16),
% 1.55/0.58    inference(avatar_split_clause,[],[f325,f155,f102,f350])).
% 1.55/0.58  fof(f102,plain,(
% 1.55/0.58    spl6_8 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 1.55/0.58  fof(f155,plain,(
% 1.55/0.58    spl6_16 <=> sK1 = u1_struct_0(sK0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 1.55/0.58  fof(f325,plain,(
% 1.55/0.58    v1_subset_1(sK1,sK1) | (~spl6_8 | ~spl6_16)),
% 1.55/0.58    inference(backward_demodulation,[],[f103,f157])).
% 1.55/0.58  fof(f157,plain,(
% 1.55/0.58    sK1 = u1_struct_0(sK0) | ~spl6_16),
% 1.55/0.58    inference(avatar_component_clause,[],[f155])).
% 1.55/0.58  fof(f103,plain,(
% 1.55/0.58    v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_8),
% 1.55/0.58    inference(avatar_component_clause,[],[f102])).
% 1.55/0.58  fof(f323,plain,(
% 1.55/0.58    sK1 != u1_struct_0(sK0) | v1_xboole_0(sK1) | ~v1_xboole_0(u1_struct_0(sK0))),
% 1.55/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.55/0.58  fof(f317,plain,(
% 1.55/0.58    spl6_23 | ~spl6_5 | ~spl6_24),
% 1.55/0.58    inference(avatar_split_clause,[],[f313,f280,f87,f268])).
% 1.55/0.58  fof(f268,plain,(
% 1.55/0.58    spl6_23 <=> r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.55/0.58  fof(f87,plain,(
% 1.55/0.58    spl6_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.55/0.58  fof(f280,plain,(
% 1.55/0.58    spl6_24 <=> r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.55/0.58  fof(f313,plain,(
% 1.55/0.58    r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | (~spl6_5 | ~spl6_24)),
% 1.55/0.58    inference(resolution,[],[f281,f167])).
% 1.55/0.58  fof(f167,plain,(
% 1.55/0.58    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,u1_struct_0(sK0))) ) | ~spl6_5),
% 1.55/0.58    inference(resolution,[],[f55,f89])).
% 1.55/0.58  fof(f89,plain,(
% 1.55/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_5),
% 1.55/0.58    inference(avatar_component_clause,[],[f87])).
% 1.55/0.58  fof(f55,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f28])).
% 1.55/0.58  fof(f28,plain,(
% 1.55/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f2])).
% 1.55/0.58  fof(f2,axiom,(
% 1.55/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.55/0.58  fof(f281,plain,(
% 1.55/0.58    r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~spl6_24),
% 1.55/0.58    inference(avatar_component_clause,[],[f280])).
% 1.55/0.58  fof(f295,plain,(
% 1.55/0.58    spl6_25),
% 1.55/0.58    inference(avatar_contradiction_clause,[],[f294])).
% 1.55/0.58  fof(f294,plain,(
% 1.55/0.58    $false | spl6_25),
% 1.55/0.58    inference(resolution,[],[f286,f152])).
% 1.55/0.58  fof(f286,plain,(
% 1.55/0.58    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_25),
% 1.55/0.58    inference(avatar_component_clause,[],[f284])).
% 1.55/0.58  fof(f284,plain,(
% 1.55/0.58    spl6_25 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.55/0.58  fof(f293,plain,(
% 1.55/0.58    ~spl6_21 | ~spl6_9 | ~spl6_10 | spl6_24 | ~spl6_20 | ~spl6_22),
% 1.55/0.58    inference(avatar_split_clause,[],[f292,f263,f239,f280,f113,f106,f256])).
% 1.55/0.58  fof(f256,plain,(
% 1.55/0.58    spl6_21 <=> m1_subset_1(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.55/0.58  fof(f106,plain,(
% 1.55/0.58    spl6_9 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.55/0.58  fof(f113,plain,(
% 1.55/0.58    spl6_10 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.55/0.58  fof(f239,plain,(
% 1.55/0.58    spl6_20 <=> ! [X3,X4] : (~m1_subset_1(X3,u1_struct_0(sK0)) | r2_hidden(X4,sK1) | ~r1_orders_2(sK0,X3,X4) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0)))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 1.55/0.58  fof(f263,plain,(
% 1.55/0.58    spl6_22 <=> r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.55/0.58  fof(f292,plain,(
% 1.55/0.58    r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | (~spl6_20 | ~spl6_22)),
% 1.55/0.58    inference(resolution,[],[f265,f240])).
% 1.55/0.58  fof(f240,plain,(
% 1.55/0.58    ( ! [X4,X3] : (~r1_orders_2(sK0,X3,X4) | r2_hidden(X4,sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | ~m1_subset_1(X4,u1_struct_0(sK0))) ) | ~spl6_20),
% 1.55/0.58    inference(avatar_component_clause,[],[f239])).
% 1.55/0.58  fof(f265,plain,(
% 1.55/0.58    r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) | ~spl6_22),
% 1.55/0.58    inference(avatar_component_clause,[],[f263])).
% 1.55/0.58  fof(f287,plain,(
% 1.55/0.58    spl6_16 | ~spl6_24 | ~spl6_5 | ~spl6_25 | ~spl6_23),
% 1.55/0.58    inference(avatar_split_clause,[],[f275,f268,f284,f87,f280,f155])).
% 1.55/0.58  fof(f275,plain,(
% 1.55/0.58    ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),sK1) | sK1 = u1_struct_0(sK0) | ~spl6_23),
% 1.55/0.58    inference(resolution,[],[f270,f57])).
% 1.55/0.58  fof(f57,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK4(X0,X1,X2),X1) | X1 = X2) )),
% 1.55/0.58    inference(cnf_transformation,[],[f30])).
% 1.55/0.58  fof(f30,plain,(
% 1.55/0.58    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.58    inference(flattening,[],[f29])).
% 1.55/0.58  fof(f29,plain,(
% 1.55/0.58    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f3])).
% 1.55/0.58  fof(f3,axiom,(
% 1.55/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).
% 1.55/0.58  fof(f270,plain,(
% 1.55/0.58    r2_hidden(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl6_23),
% 1.55/0.58    inference(avatar_component_clause,[],[f268])).
% 1.55/0.58  fof(f266,plain,(
% 1.55/0.58    spl6_22 | spl6_4 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_21),
% 1.55/0.58    inference(avatar_split_clause,[],[f260,f256,f77,f72,f67,f82,f263])).
% 1.55/0.58  fof(f82,plain,(
% 1.55/0.58    spl6_4 <=> v2_struct_0(sK0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.55/0.58  fof(f67,plain,(
% 1.55/0.58    spl6_1 <=> l1_orders_2(sK0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.55/0.58  fof(f72,plain,(
% 1.55/0.58    spl6_2 <=> v1_yellow_0(sK0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.55/0.58  fof(f77,plain,(
% 1.55/0.58    spl6_3 <=> v5_orders_2(sK0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.55/0.58  fof(f260,plain,(
% 1.55/0.58    ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | r1_orders_2(sK0,k3_yellow_0(sK0),sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0))) | ~spl6_21),
% 1.55/0.58    inference(resolution,[],[f258,f50])).
% 1.55/0.58  fof(f50,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | r1_orders_2(X0,k3_yellow_0(X0),X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f23])).
% 1.55/0.58  fof(f23,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.55/0.58    inference(flattening,[],[f22])).
% 1.55/0.58  fof(f22,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f9])).
% 1.55/0.58  fof(f9,axiom,(
% 1.55/0.58    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).
% 1.55/0.58  fof(f258,plain,(
% 1.55/0.58    m1_subset_1(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl6_21),
% 1.55/0.58    inference(avatar_component_clause,[],[f256])).
% 1.55/0.58  fof(f259,plain,(
% 1.55/0.58    spl6_16 | spl6_21 | ~spl6_5),
% 1.55/0.58    inference(avatar_split_clause,[],[f252,f87,f256,f155])).
% 1.55/0.58  fof(f252,plain,(
% 1.55/0.58    m1_subset_1(sK4(u1_struct_0(sK0),sK1,u1_struct_0(sK0)),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0) | ~spl6_5),
% 1.55/0.58    inference(resolution,[],[f212,f152])).
% 1.55/0.58  fof(f212,plain,(
% 1.55/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK4(u1_struct_0(sK0),sK1,X2),u1_struct_0(sK0)) | sK1 = X2) ) | ~spl6_5),
% 1.55/0.58    inference(resolution,[],[f58,f89])).
% 1.55/0.58  fof(f58,plain,(
% 1.55/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(sK4(X0,X1,X2),X0) | X1 = X2) )),
% 1.55/0.58    inference(cnf_transformation,[],[f30])).
% 1.55/0.58  fof(f241,plain,(
% 1.55/0.58    ~spl6_6 | spl6_20 | ~spl6_1 | ~spl6_5),
% 1.55/0.58    inference(avatar_split_clause,[],[f236,f87,f67,f239,f92])).
% 1.55/0.58  fof(f92,plain,(
% 1.55/0.58    spl6_6 <=> v13_waybel_0(sK1,sK0)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.55/0.58  fof(f236,plain,(
% 1.55/0.58    ( ! [X4,X3] : (~l1_orders_2(sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1) | ~r1_orders_2(sK0,X3,X4) | r2_hidden(X4,sK1) | ~v13_waybel_0(sK1,sK0)) ) | ~spl6_5),
% 1.55/0.58    inference(resolution,[],[f48,f89])).
% 1.55/0.58  fof(f48,plain,(
% 1.55/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f21])).
% 1.55/0.58  fof(f21,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.55/0.58    inference(flattening,[],[f20])).
% 1.55/0.58  fof(f20,plain,(
% 1.55/0.58    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f10])).
% 1.55/0.58  fof(f10,axiom,(
% 1.55/0.58    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.55/0.58  fof(f166,plain,(
% 1.55/0.58    sK1 != u1_struct_0(sK0) | r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.55/0.58    introduced(theory_tautology_sat_conflict,[])).
% 1.55/0.58  fof(f158,plain,(
% 1.55/0.58    spl6_8 | spl6_16 | ~spl6_5),
% 1.55/0.58    inference(avatar_split_clause,[],[f153,f87,f155,f102])).
% 1.55/0.58  fof(f153,plain,(
% 1.55/0.58    sK1 = u1_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_5),
% 1.55/0.58    inference(resolution,[],[f53,f89])).
% 1.55/0.58  fof(f53,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f27])).
% 1.55/0.58  fof(f143,plain,(
% 1.55/0.58    spl6_14 | spl6_15 | ~spl6_10),
% 1.55/0.58    inference(avatar_split_clause,[],[f125,f113,f140,f136])).
% 1.55/0.58  fof(f136,plain,(
% 1.55/0.58    spl6_14 <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.55/0.58  fof(f140,plain,(
% 1.55/0.58    spl6_15 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.55/0.58  fof(f125,plain,(
% 1.55/0.58    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl6_10),
% 1.55/0.58    inference(resolution,[],[f52,f115])).
% 1.55/0.58  fof(f115,plain,(
% 1.55/0.58    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl6_10),
% 1.55/0.58    inference(avatar_component_clause,[],[f113])).
% 1.55/0.58  fof(f52,plain,(
% 1.55/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.55/0.58    inference(cnf_transformation,[],[f26])).
% 1.55/0.58  fof(f26,plain,(
% 1.55/0.58    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.55/0.58    inference(flattening,[],[f25])).
% 1.55/0.58  fof(f25,plain,(
% 1.55/0.58    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.55/0.58    inference(ennf_transformation,[],[f5])).
% 1.55/0.58  fof(f5,axiom,(
% 1.55/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.55/0.58  fof(f116,plain,(
% 1.55/0.58    spl6_10 | ~spl6_1),
% 1.55/0.58    inference(avatar_split_clause,[],[f111,f67,f113])).
% 1.55/0.58  fof(f111,plain,(
% 1.55/0.58    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl6_1),
% 1.55/0.58    inference(resolution,[],[f43,f69])).
% 1.55/0.58  fof(f69,plain,(
% 1.55/0.58    l1_orders_2(sK0) | ~spl6_1),
% 1.55/0.58    inference(avatar_component_clause,[],[f67])).
% 1.55/0.58  fof(f43,plain,(
% 1.55/0.58    ( ! [X0] : (~l1_orders_2(X0) | m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))) )),
% 1.55/0.58    inference(cnf_transformation,[],[f19])).
% 1.55/0.58  fof(f19,plain,(
% 1.55/0.58    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.55/0.58    inference(ennf_transformation,[],[f8])).
% 1.55/0.58  fof(f8,axiom,(
% 1.55/0.58    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 1.55/0.58  fof(f110,plain,(
% 1.55/0.58    spl6_8 | ~spl6_9),
% 1.55/0.58    inference(avatar_split_clause,[],[f34,f106,f102])).
% 1.55/0.58  fof(f34,plain,(
% 1.55/0.58    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.55/0.58    inference(cnf_transformation,[],[f18])).
% 1.55/0.58  fof(f18,plain,(
% 1.55/0.58    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0))),
% 1.55/0.58    inference(flattening,[],[f17])).
% 1.55/0.58  fof(f17,plain,(
% 1.55/0.58    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.55/0.58    inference(ennf_transformation,[],[f16])).
% 1.55/0.58  fof(f16,plain,(
% 1.55/0.58    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.55/0.58    inference(pure_predicate_removal,[],[f15])).
% 1.55/0.58  fof(f15,plain,(
% 1.55/0.58    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.55/0.58    inference(pure_predicate_removal,[],[f14])).
% 1.55/0.58  fof(f14,plain,(
% 1.55/0.58    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.55/0.58    inference(pure_predicate_removal,[],[f13])).
% 1.55/0.58  fof(f13,negated_conjecture,(
% 1.55/0.58    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.55/0.58    inference(negated_conjecture,[],[f12])).
% 1.55/0.58  fof(f12,conjecture,(
% 1.55/0.58    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.55/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.55/0.58  fof(f109,plain,(
% 1.55/0.58    ~spl6_8 | spl6_9),
% 1.55/0.58    inference(avatar_split_clause,[],[f35,f106,f102])).
% 1.55/0.58  fof(f35,plain,(
% 1.55/0.58    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.55/0.58    inference(cnf_transformation,[],[f18])).
% 1.55/0.58  fof(f100,plain,(
% 1.55/0.58    ~spl6_7),
% 1.55/0.58    inference(avatar_split_clause,[],[f36,f97])).
% 1.55/0.58  fof(f97,plain,(
% 1.55/0.58    spl6_7 <=> v1_xboole_0(sK1)),
% 1.55/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.55/0.58  fof(f36,plain,(
% 1.55/0.58    ~v1_xboole_0(sK1)),
% 1.55/0.58    inference(cnf_transformation,[],[f18])).
% 1.55/0.58  fof(f95,plain,(
% 1.55/0.58    spl6_6),
% 1.55/0.58    inference(avatar_split_clause,[],[f37,f92])).
% 1.55/0.58  fof(f37,plain,(
% 1.55/0.58    v13_waybel_0(sK1,sK0)),
% 1.55/0.58    inference(cnf_transformation,[],[f18])).
% 1.55/0.58  fof(f90,plain,(
% 1.55/0.58    spl6_5),
% 1.55/0.58    inference(avatar_split_clause,[],[f38,f87])).
% 1.55/0.58  fof(f38,plain,(
% 1.55/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.58    inference(cnf_transformation,[],[f18])).
% 1.55/0.58  fof(f85,plain,(
% 1.55/0.58    ~spl6_4),
% 1.55/0.58    inference(avatar_split_clause,[],[f39,f82])).
% 1.55/0.58  fof(f39,plain,(
% 1.55/0.58    ~v2_struct_0(sK0)),
% 1.55/0.58    inference(cnf_transformation,[],[f18])).
% 1.55/0.58  fof(f80,plain,(
% 1.55/0.58    spl6_3),
% 1.55/0.58    inference(avatar_split_clause,[],[f40,f77])).
% 1.55/0.58  fof(f40,plain,(
% 1.55/0.58    v5_orders_2(sK0)),
% 1.55/0.58    inference(cnf_transformation,[],[f18])).
% 1.55/0.58  fof(f75,plain,(
% 1.55/0.58    spl6_2),
% 1.55/0.58    inference(avatar_split_clause,[],[f41,f72])).
% 1.55/0.58  fof(f41,plain,(
% 1.55/0.58    v1_yellow_0(sK0)),
% 1.55/0.58    inference(cnf_transformation,[],[f18])).
% 1.55/0.58  fof(f70,plain,(
% 1.55/0.58    spl6_1),
% 1.55/0.58    inference(avatar_split_clause,[],[f42,f67])).
% 1.55/0.58  fof(f42,plain,(
% 1.55/0.58    l1_orders_2(sK0)),
% 1.55/0.58    inference(cnf_transformation,[],[f18])).
% 1.55/0.58  % SZS output end Proof for theBenchmark
% 1.55/0.58  % (28494)------------------------------
% 1.55/0.58  % (28494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (28494)Termination reason: Refutation
% 1.55/0.58  
% 1.55/0.58  % (28494)Memory used [KB]: 11001
% 1.55/0.58  % (28494)Time elapsed: 0.131 s
% 1.55/0.58  % (28494)------------------------------
% 1.55/0.58  % (28494)------------------------------
% 1.55/0.58  % (28477)Success in time 0.221 s
%------------------------------------------------------------------------------
