%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t135_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:17 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 318 expanded)
%              Number of leaves         :   34 ( 119 expanded)
%              Depth                    :   11
%              Number of atoms          :  446 (1087 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f103,f110,f117,f124,f134,f146,f166,f187,f195,f224,f241,f254,f261,f268,f275,f286,f295,f297,f299,f301,f303,f307])).

fof(f307,plain,
    ( ~ spl4_0
    | ~ spl4_8
    | spl4_13
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f305,f95])).

fof(f95,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f305,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f304,f123])).

fof(f123,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f304,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f294,f285])).

fof(f285,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl4_32
  <=> r7_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f294,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl4_13 ),
    inference(resolution,[],[f75,f145])).

fof(f145,plain,
    ( ~ v6_orders_2(sK1,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f144])).

fof(f144,plain,
    ( spl4_13
  <=> ~ v6_orders_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v6_orders_2(X1,X0)
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t135_orders_2.p',d11_orders_2)).

fof(f303,plain,
    ( ~ spl4_0
    | ~ spl4_8
    | spl4_13
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f302])).

fof(f302,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f289,f123])).

fof(f289,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_0
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f95,f145,f285,f75])).

fof(f301,plain,
    ( ~ spl4_0
    | ~ spl4_8
    | spl4_13
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f300])).

fof(f300,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f290,f285])).

fof(f290,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f95,f145,f123,f75])).

fof(f299,plain,
    ( ~ spl4_0
    | ~ spl4_8
    | spl4_13
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f291,f145])).

fof(f291,plain,
    ( v6_orders_2(sK1,sK0)
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f95,f285,f123,f75])).

fof(f297,plain,
    ( ~ spl4_0
    | ~ spl4_8
    | spl4_13
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f292,f95])).

fof(f292,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f145,f285,f123,f75])).

fof(f295,plain,
    ( ~ spl4_0
    | ~ spl4_8
    | spl4_13
    | ~ spl4_32 ),
    inference(avatar_contradiction_clause,[],[f293])).

fof(f293,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_32 ),
    inference(unit_resulting_resolution,[],[f95,f145,f285,f123,f75])).

fof(f286,plain,
    ( spl4_32
    | ~ spl4_20
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f278,f273,f252,f222,f284])).

fof(f222,plain,
    ( spl4_20
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f252,plain,
    ( spl4_24
  <=> r6_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f273,plain,
    ( spl4_30
  <=> r1_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f278,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_20
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f277,f223])).

fof(f223,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f222])).

fof(f277,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f276,f274])).

fof(f274,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f273])).

fof(f276,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_24 ),
    inference(resolution,[],[f253,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r6_relat_2(X1,X0)
      | r7_relat_2(X1,X0)
      | ~ r1_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r7_relat_2(X1,X0)
      <=> ( r6_relat_2(X1,X0)
          & r1_relat_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t135_orders_2.p',t92_orders_1)).

fof(f253,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f252])).

fof(f275,plain,
    ( spl4_30
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f228,f222,f115,f273])).

fof(f115,plain,
    ( spl4_6
  <=> r3_orders_1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f228,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f116,f223,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r3_orders_1(X0,X1)
      | r1_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_orders_1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r3_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r3_orders_1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r3_orders_1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r3_orders_1(X0,X1)
        <=> ( r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t135_orders_2.p',d8_orders_1)).

fof(f116,plain,
    ( r3_orders_1(u1_orders_2(sK0),sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f268,plain,
    ( spl4_28
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f227,f222,f115,f266])).

fof(f266,plain,
    ( spl4_28
  <=> r8_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f227,plain,
    ( r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f116,f223,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r3_orders_1(X0,X1)
      | r8_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f261,plain,
    ( spl4_26
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f226,f222,f115,f259])).

fof(f259,plain,
    ( spl4_26
  <=> r4_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f226,plain,
    ( r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f116,f223,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r3_orders_1(X0,X1)
      | r4_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f254,plain,
    ( spl4_24
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f225,f222,f115,f252])).

fof(f225,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f116,f223,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r3_orders_1(X0,X1)
      | r6_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f241,plain,
    ( spl4_22
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f215,f108,f239])).

fof(f239,plain,
    ( spl4_22
  <=> v1_relat_1(u1_orders_2(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f108,plain,
    ( spl4_4
  <=> l1_orders_2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f215,plain,
    ( v1_relat_1(u1_orders_2(sK3))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f109,f212])).

fof(f212,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_relat_1(u1_orders_2(X0)) ) ),
    inference(resolution,[],[f73,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t135_orders_2.p',cc1_relset_1)).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t135_orders_2.p',dt_u1_orders_2)).

fof(f109,plain,
    ( l1_orders_2(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f224,plain,
    ( spl4_20
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f214,f94,f222])).

fof(f214,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f95,f212])).

fof(f195,plain,
    ( spl4_18
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f188,f185,f193])).

fof(f193,plain,
    ( spl4_18
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f185,plain,
    ( spl4_16
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f188,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(superposition,[],[f77,f186])).

fof(f186,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f185])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t135_orders_2.p',existence_m1_subset_1)).

fof(f187,plain,
    ( spl4_16
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f172,f164,f101,f185])).

fof(f101,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f164,plain,
    ( spl4_14
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f172,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f165,f127])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f125,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t135_orders_2.p',t6_boole)).

fof(f125,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f102,f76])).

fof(f102,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f165,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f164])).

fof(f166,plain,
    ( spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f159,f101,f164])).

fof(f159,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f77,f158,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t135_orders_2.p',t2_subset)).

fof(f158,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f102,f77,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t135_orders_2.p',t5_subset)).

fof(f146,plain,
    ( ~ spl4_13
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f66,f119,f144])).

fof(f119,plain,
    ( spl4_9
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f66,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(sK1,sK0) )
    & r3_orders_1(u1_orders_2(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X1,X0) )
            & r3_orders_1(u1_orders_2(X0),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v6_orders_2(X1,sK0) )
          & r3_orders_1(u1_orders_2(sK0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v6_orders_2(sK1,X0) )
        & r3_orders_1(u1_orders_2(X0),sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r3_orders_1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r3_orders_1(u1_orders_2(X0),X1)
             => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X1,X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f32])).

fof(f32,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r3_orders_1(u1_orders_2(X0),X1)
             => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X1,X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f31])).

fof(f31,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r3_orders_1(u1_orders_2(X0),X1)
             => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X1,X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f30])).

fof(f30,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r3_orders_1(u1_orders_2(X0),X1)
             => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X1,X0) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r3_orders_1(u1_orders_2(X0),X1)
             => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r3_orders_1(u1_orders_2(X0),X1)
           => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t135_orders_2.p',t135_orders_2)).

fof(f134,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f125,f101,f132])).

fof(f132,plain,
    ( spl4_10
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f124,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f64,f122])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f117,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f65,f115])).

fof(f65,plain,(
    r3_orders_1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f110,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f89,f108])).

fof(f89,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    l1_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f61])).

fof(f61,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK3) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t135_orders_2.p',existence_l1_orders_2)).

fof(f103,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f67,f101])).

fof(f67,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t135_orders_2.p',dt_o_0_0_xboole_0)).

fof(f96,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f63,f94])).

fof(f63,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
