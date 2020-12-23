%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : yellow19__t25_yellow19.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:50 EDT 2019

% Result     : Theorem 6.74s
% Output     : Refutation 6.74s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 898 expanded)
%              Number of leaves         :   27 ( 227 expanded)
%              Depth                    :   12
%              Number of atoms          :  541 (6893 expanded)
%              Number of equality atoms :   13 ( 120 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1658,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f149,f156,f163,f180,f198,f218,f234,f241,f262,f422,f692,f732,f804,f1034,f1044,f1528,f1563,f1657])).

fof(f1657,plain,
    ( ~ spl11_0
    | spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16 ),
    inference(avatar_contradiction_clause,[],[f1650])).

fof(f1650,plain,
    ( $false
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_9
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16 ),
    inference(unit_resulting_resolution,[],[f111,f179,f1637,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t25_yellow19.p',d3_tarski)).

fof(f1637,plain,
    ( r2_hidden(sK3,sK1)
    | ~ spl11_0
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16 ),
    inference(forward_demodulation,[],[f1634,f1566])).

fof(f1566,plain,
    ( k2_pre_topc(sK0,sK1) = sK1
    | ~ spl11_0 ),
    inference(unit_resulting_resolution,[],[f73,f70,f139,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t25_yellow19.p',t52_pre_topc)).

fof(f139,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl11_0
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f70,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r3_waybel_9(X0,X2,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_waybel_0(X0,X2,X1)
                | ~ l1_waybel_0(X2,X0)
                | ~ v7_waybel_0(X2)
                | ~ v4_orders_2(X2)
                | v2_struct_0(X2) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> ! [X2] :
                  ( ( l1_waybel_0(X2,X0)
                    & v7_waybel_0(X2)
                    & v4_orders_2(X2)
                    & ~ v2_struct_0(X2) )
                 => ( r1_waybel_0(X0,X2,X1)
                   => ! [X3] :
                        ( m1_subset_1(X3,u1_struct_0(X0))
                       => ( r3_waybel_9(X0,X2,X3)
                         => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> ! [X2] :
                ( ( l1_waybel_0(X2,X0)
                  & v7_waybel_0(X2)
                  & v4_orders_2(X2)
                  & ~ v2_struct_0(X2) )
               => ( r1_waybel_0(X0,X2,X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r3_waybel_9(X0,X2,X3)
                       => r2_hidden(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t25_yellow19.p',t25_yellow19)).

fof(f73,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f1634,plain,
    ( r2_hidden(sK3,k2_pre_topc(sK0,sK1))
    | ~ spl11_3
    | ~ spl11_4
    | ~ spl11_6
    | ~ spl11_10
    | ~ spl11_12
    | ~ spl11_14
    | ~ spl11_16 ),
    inference(unit_resulting_resolution,[],[f73,f72,f162,f148,f71,f155,f197,f233,f217,f70,f240,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v7_waybel_0(X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X3)
      | ~ v4_orders_2(X3)
      | v2_struct_0(X0)
      | ~ l1_waybel_0(X3,X0)
      | ~ r1_waybel_0(X0,X3,X1)
      | ~ r3_waybel_9(X0,X3,X2)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ? [X3] :
                    ( r3_waybel_9(X0,X3,X2)
                    & r1_waybel_0(X0,X3,X1)
                    & l1_waybel_0(X3,X0)
                    & v7_waybel_0(X3)
                    & v4_orders_2(X3)
                    & ~ v2_struct_0(X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t25_yellow19.p',t23_yellow19)).

fof(f240,plain,
    ( r1_waybel_0(sK0,sK2,sK1)
    | ~ spl11_16 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl11_16
  <=> r1_waybel_0(sK0,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_16])])).

fof(f217,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ spl11_12 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl11_12
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_12])])).

fof(f233,plain,
    ( r3_waybel_9(sK0,sK2,sK3)
    | ~ spl11_14 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl11_14
  <=> r3_waybel_9(sK0,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_14])])).

fof(f197,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ spl11_10 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl11_10
  <=> l1_waybel_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_10])])).

fof(f155,plain,
    ( v4_orders_2(sK2)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl11_4
  <=> v4_orders_2(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f71,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f148,plain,
    ( ~ v2_struct_0(sK2)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl11_3
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f162,plain,
    ( v7_waybel_0(sK2)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl11_6
  <=> v7_waybel_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f72,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f179,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl11_9
  <=> ~ r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t25_yellow19.p',d10_xboole_0)).

fof(f1563,plain,
    ( spl11_1
    | ~ spl11_92 ),
    inference(avatar_contradiction_clause,[],[f1556])).

fof(f1556,plain,
    ( $false
    | ~ spl11_1
    | ~ spl11_92 ),
    inference(unit_resulting_resolution,[],[f189,f389,f404,f403,f402,f188,f405,f1527])).

fof(f1527,plain,
    ( ! [X0] :
        ( ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ v4_orders_2(sK4(sK0,sK1,X0))
        | ~ v7_waybel_0(sK4(sK0,sK1,X0)) )
    | ~ spl11_92 ),
    inference(avatar_component_clause,[],[f1526])).

fof(f1526,plain,
    ( spl11_92
  <=> ! [X0] :
        ( ~ v4_orders_2(sK4(sK0,sK1,X0))
        | r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | ~ v7_waybel_0(sK4(sK0,sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_92])])).

fof(f405,plain,
    ( l1_waybel_0(sK4(sK0,sK1,sK10(k2_pre_topc(sK0,sK1),sK1)),sK0)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f71,f72,f73,f70,f188,f389,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | l1_waybel_0(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f188,plain,
    ( r2_hidden(sK10(k2_pre_topc(sK0,sK1),sK1),k2_pre_topc(sK0,sK1))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f184,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK10(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f184,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f165,f168,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f168,plain,(
    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f73,f70,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t25_yellow19.p',t48_pre_topc)).

fof(f165,plain,
    ( k2_pre_topc(sK0,sK1) != sK1
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f72,f73,f142,f70,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | k2_pre_topc(X0,X1) != X1
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f142,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl11_1
  <=> ~ v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f402,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1,sK10(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f73,f71,f72,f70,f188,f389,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(sK4(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f403,plain,
    ( v4_orders_2(sK4(sK0,sK1,sK10(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f73,f71,f72,f70,f188,f389,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(sK4(X0,X1,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f404,plain,
    ( v7_waybel_0(sK4(sK0,sK1,sK10(k2_pre_topc(sK0,sK1),sK1)))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f71,f72,f73,f70,f188,f389,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v7_waybel_0(sK4(X0,X1,X2))
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f389,plain,
    ( m1_subset_1(sK10(k2_pre_topc(sK0,sK1),sK1),u1_struct_0(sK0))
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f167,f188,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t25_yellow19.p',t4_subset)).

fof(f167,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f73,f70,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t25_yellow19.p',dt_k2_pre_topc)).

fof(f189,plain,
    ( ~ r2_hidden(sK10(k2_pre_topc(sK0,sK1),sK1),sK1)
    | ~ spl11_1 ),
    inference(unit_resulting_resolution,[],[f184,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f1528,plain,
    ( ~ spl11_69
    | spl11_92
    | ~ spl11_48
    | ~ spl11_70 ),
    inference(avatar_split_clause,[],[f1082,f1032,f802,f1526,f1029])).

fof(f1029,plain,
    ( spl11_69
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_69])])).

fof(f802,plain,
    ( spl11_48
  <=> ! [X7,X6] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X7,k2_pre_topc(sK0,X6))
        | r3_waybel_9(sK0,sK4(sK0,X6,X7),X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_48])])).

fof(f1032,plain,
    ( spl11_70
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ v4_orders_2(sK4(sK0,sK1,X0))
        | ~ v7_waybel_0(sK4(sK0,sK1,X0))
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X1)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_70])])).

fof(f1082,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK0,sK1,X0))
        | ~ v7_waybel_0(sK4(sK0,sK1,X0))
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl11_48
    | ~ spl11_70 ),
    inference(duplicate_literal_removal,[],[f1081])).

fof(f1081,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK4(sK0,sK1,X0))
        | ~ v7_waybel_0(sK4(sK0,sK1,X0))
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_48
    | ~ spl11_70 ),
    inference(resolution,[],[f1033,f803])).

fof(f803,plain,
    ( ! [X6,X7] :
        ( r3_waybel_9(sK0,sK4(sK0,X6,X7),X7)
        | ~ r2_hidden(X7,k2_pre_topc(sK0,X6))
        | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl11_48 ),
    inference(avatar_component_clause,[],[f802])).

fof(f1033,plain,
    ( ! [X0,X1] :
        ( ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X1)
        | ~ v4_orders_2(sK4(sK0,sK1,X0))
        | ~ v7_waybel_0(sK4(sK0,sK1,X0))
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_70 ),
    inference(avatar_component_clause,[],[f1032])).

fof(f1044,plain,(
    spl11_69 ),
    inference(avatar_contradiction_clause,[],[f1037])).

fof(f1037,plain,
    ( $false
    | ~ spl11_69 ),
    inference(unit_resulting_resolution,[],[f169,f1030,f105])).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/yellow19__t25_yellow19.p',t3_subset)).

fof(f1030,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl11_69 ),
    inference(avatar_component_clause,[],[f1029])).

fof(f169,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f70,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f1034,plain,
    ( ~ spl11_69
    | spl11_70
    | ~ spl11_18
    | ~ spl11_46 ),
    inference(avatar_split_clause,[],[f777,f730,f260,f1032,f1029])).

fof(f260,plain,
    ( spl11_18
  <=> ! [X3,X2] :
        ( v2_struct_0(X2)
        | r2_hidden(X3,sK1)
        | ~ r3_waybel_9(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r1_waybel_0(sK0,X2,sK1)
        | ~ l1_waybel_0(X2,sK0)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f730,plain,
    ( spl11_46
  <=> ! [X5,X4] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X5,k2_pre_topc(sK0,X4))
        | r1_waybel_0(sK0,sK4(sK0,X4,X5),X4)
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_46])])).

fof(f777,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ r3_waybel_9(sK0,sK4(sK0,sK1,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK4(sK0,sK1,X0))
        | ~ l1_waybel_0(sK4(sK0,sK1,X0),sK0)
        | ~ v7_waybel_0(sK4(sK0,sK1,X0))
        | ~ v4_orders_2(sK4(sK0,sK1,X0)) )
    | ~ spl11_18
    | ~ spl11_46 ),
    inference(resolution,[],[f731,f261])).

fof(f261,plain,
    ( ! [X2,X3] :
        ( ~ r1_waybel_0(sK0,X2,sK1)
        | r2_hidden(X3,sK1)
        | ~ r3_waybel_9(sK0,X2,X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | v2_struct_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | ~ v7_waybel_0(X2)
        | ~ v4_orders_2(X2) )
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f260])).

fof(f731,plain,
    ( ! [X4,X5] :
        ( r1_waybel_0(sK0,sK4(sK0,X4,X5),X4)
        | ~ r2_hidden(X5,k2_pre_topc(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X5,u1_struct_0(sK0)) )
    | ~ spl11_46 ),
    inference(avatar_component_clause,[],[f730])).

fof(f804,plain,
    ( spl11_48
    | spl11_38
    | ~ spl11_31 ),
    inference(avatar_split_clause,[],[f120,f416,f636,f802])).

fof(f636,plain,
    ( spl11_38
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_38])])).

fof(f416,plain,
    ( spl11_31
  <=> ~ v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_31])])).

fof(f120,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,u1_struct_0(sK0))
      | r3_waybel_9(sK0,sK4(sK0,X6,X7),X7)
      | ~ r2_hidden(X7,k2_pre_topc(sK0,X6)) ) ),
    inference(resolution,[],[f73,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_waybel_9(X0,sK4(X0,X1,X2),X2)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f732,plain,
    ( spl11_46
    | spl11_38
    | ~ spl11_31 ),
    inference(avatar_split_clause,[],[f119,f416,f636,f730])).

fof(f119,plain,(
    ! [X4,X5] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r1_waybel_0(sK0,sK4(sK0,X4,X5),X4)
      | ~ r2_hidden(X5,k2_pre_topc(sK0,X4)) ) ),
    inference(resolution,[],[f73,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_waybel_0(X0,sK4(X0,X1,X2),X1)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f692,plain,(
    ~ spl11_38 ),
    inference(avatar_contradiction_clause,[],[f689])).

fof(f689,plain,
    ( $false
    | ~ spl11_38 ),
    inference(unit_resulting_resolution,[],[f71,f637])).

fof(f637,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_38 ),
    inference(avatar_component_clause,[],[f636])).

fof(f422,plain,(
    spl11_31 ),
    inference(avatar_contradiction_clause,[],[f419])).

fof(f419,plain,
    ( $false
    | ~ spl11_31 ),
    inference(unit_resulting_resolution,[],[f72,f417])).

fof(f417,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl11_31 ),
    inference(avatar_component_clause,[],[f416])).

fof(f262,plain,
    ( spl11_0
    | spl11_18 ),
    inference(avatar_split_clause,[],[f61,f260,f138])).

fof(f61,plain,(
    ! [X2,X3] :
      ( v2_struct_0(X2)
      | ~ v4_orders_2(X2)
      | ~ v7_waybel_0(X2)
      | ~ l1_waybel_0(X2,sK0)
      | ~ r1_waybel_0(sK0,X2,sK1)
      | ~ m1_subset_1(X3,u1_struct_0(sK0))
      | ~ r3_waybel_9(sK0,X2,X3)
      | r2_hidden(X3,sK1)
      | v4_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f241,plain,
    ( ~ spl11_1
    | spl11_16 ),
    inference(avatar_split_clause,[],[f69,f239,f141])).

fof(f69,plain,
    ( r1_waybel_0(sK0,sK2,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f234,plain,
    ( ~ spl11_1
    | spl11_14 ),
    inference(avatar_split_clause,[],[f63,f232,f141])).

fof(f63,plain,
    ( r3_waybel_9(sK0,sK2,sK3)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f218,plain,
    ( ~ spl11_1
    | spl11_12 ),
    inference(avatar_split_clause,[],[f62,f216,f141])).

fof(f62,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f198,plain,
    ( ~ spl11_1
    | spl11_10 ),
    inference(avatar_split_clause,[],[f68,f196,f141])).

fof(f68,plain,
    ( l1_waybel_0(sK2,sK0)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f180,plain,
    ( ~ spl11_1
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f64,f178,f141])).

fof(f64,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f163,plain,
    ( ~ spl11_1
    | spl11_6 ),
    inference(avatar_split_clause,[],[f67,f161,f141])).

fof(f67,plain,
    ( v7_waybel_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f156,plain,
    ( ~ spl11_1
    | spl11_4 ),
    inference(avatar_split_clause,[],[f66,f154,f141])).

fof(f66,plain,
    ( v4_orders_2(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f149,plain,
    ( ~ spl11_1
    | ~ spl11_3 ),
    inference(avatar_split_clause,[],[f65,f147,f141])).

fof(f65,plain,
    ( ~ v2_struct_0(sK2)
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
