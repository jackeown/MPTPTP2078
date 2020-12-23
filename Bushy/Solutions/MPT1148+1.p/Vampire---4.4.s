%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t40_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:20 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 231 expanded)
%              Number of leaves         :   34 (  95 expanded)
%              Depth                    :    8
%              Number of atoms          :  348 ( 779 expanded)
%              Number of equality atoms :    9 (  18 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f290,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f93,f100,f107,f114,f121,f131,f143,f157,f178,f186,f221,f240,f254,f261,f268,f275,f282,f289])).

fof(f289,plain,
    ( ~ spl4_0
    | ~ spl4_8
    | spl4_13
    | ~ spl4_20
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_13
    | ~ spl4_20
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(subsumption_resolution,[],[f285,f283])).

fof(f283,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_20
    | ~ spl4_24
    | ~ spl4_30 ),
    inference(unit_resulting_resolution,[],[f220,f253,f274,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r6_relat_2(X1,X0)
      | r7_relat_2(X1,X0)
      | ~ r1_relat_2(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( r7_relat_2(X1,X0)
          | ~ r6_relat_2(X1,X0)
          | ~ r1_relat_2(X1,X0) )
        & ( ( r6_relat_2(X1,X0)
            & r1_relat_2(X1,X0) )
          | ~ r7_relat_2(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/orders_2__t40_orders_2.p',t92_orders_1)).

fof(f274,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl4_30
  <=> r6_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f253,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl4_24
  <=> r1_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f220,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f219])).

fof(f219,plain,
    ( spl4_20
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f285,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_0
    | ~ spl4_8
    | ~ spl4_13 ),
    inference(unit_resulting_resolution,[],[f92,f142,f120,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(u1_orders_2(X0),X1)
      | v6_orders_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/orders_2__t40_orders_2.p',d11_orders_2)).

fof(f120,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl4_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f142,plain,
    ( ~ v6_orders_2(sK1,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl4_13
  <=> ~ v6_orders_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f92,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f282,plain,
    ( spl4_32
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f226,f219,f112,f280])).

fof(f280,plain,
    ( spl4_32
  <=> r1_wellord1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f112,plain,
    ( spl4_6
  <=> r2_wellord1(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f226,plain,
    ( r1_wellord1(u1_orders_2(sK0),sK1)
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f113,f220,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_wellord1(X0,X1)
      | r1_wellord1(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_wellord1(X0,X1)
            | ~ r1_wellord1(X0,X1)
            | ~ r6_relat_2(X0,X1)
            | ~ r4_relat_2(X0,X1)
            | ~ r8_relat_2(X0,X1)
            | ~ r1_relat_2(X0,X1) )
          & ( ( r1_wellord1(X0,X1)
              & r6_relat_2(X0,X1)
              & r4_relat_2(X0,X1)
              & r8_relat_2(X0,X1)
              & r1_relat_2(X0,X1) )
            | ~ r2_wellord1(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r2_wellord1(X0,X1)
        <=> ( r1_wellord1(X0,X1)
            & r6_relat_2(X0,X1)
            & r4_relat_2(X0,X1)
            & r8_relat_2(X0,X1)
            & r1_relat_2(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t40_orders_2.p',d5_wellord1)).

fof(f113,plain,
    ( r2_wellord1(u1_orders_2(sK0),sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f112])).

fof(f275,plain,
    ( spl4_30
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f225,f219,f112,f273])).

fof(f225,plain,
    ( r6_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f113,f220,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_wellord1(X0,X1)
      | r6_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f268,plain,
    ( spl4_28
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f224,f219,f112,f266])).

fof(f266,plain,
    ( spl4_28
  <=> r4_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f224,plain,
    ( r4_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f113,f220,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_wellord1(X0,X1)
      | r4_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f261,plain,
    ( spl4_26
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f223,f219,f112,f259])).

fof(f259,plain,
    ( spl4_26
  <=> r8_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f223,plain,
    ( r8_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f113,f220,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_wellord1(X0,X1)
      | r8_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f254,plain,
    ( spl4_24
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f222,f219,f112,f252])).

fof(f222,plain,
    ( r1_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl4_6
    | ~ spl4_20 ),
    inference(unit_resulting_resolution,[],[f113,f220,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_wellord1(X0,X1)
      | r1_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f240,plain,
    ( spl4_22
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f212,f105,f238])).

fof(f238,plain,
    ( spl4_22
  <=> v1_relat_1(u1_orders_2(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f105,plain,
    ( spl4_4
  <=> l1_orders_2(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f212,plain,
    ( v1_relat_1(u1_orders_2(sK3))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f106,f209])).

fof(f209,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | v1_relat_1(u1_orders_2(X0)) ) ),
    inference(resolution,[],[f70,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t40_orders_2.p',cc1_relset_1)).

fof(f70,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t40_orders_2.p',dt_u1_orders_2)).

fof(f106,plain,
    ( l1_orders_2(sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f221,plain,
    ( spl4_20
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f211,f91,f219])).

fof(f211,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl4_0 ),
    inference(unit_resulting_resolution,[],[f92,f209])).

fof(f186,plain,
    ( spl4_18
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f179,f176,f184])).

fof(f184,plain,
    ( spl4_18
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f176,plain,
    ( spl4_16
  <=> o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f179,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(superposition,[],[f74,f177])).

fof(f177,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f176])).

fof(f74,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f17,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f17,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t40_orders_2.p',existence_m1_subset_1)).

fof(f178,plain,
    ( spl4_16
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f163,f155,f98,f176])).

fof(f98,plain,
    ( spl4_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f155,plain,
    ( spl4_14
  <=> v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f163,plain,
    ( o_0_0_xboole_0 = sK2(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl4_2
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f156,f124])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f122,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t40_orders_2.p',t6_boole)).

fof(f122,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f99,f73])).

fof(f99,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f156,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f155])).

fof(f157,plain,
    ( spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f150,f98,f155])).

fof(f150,plain,
    ( v1_xboole_0(sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f74,f149,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox2/benchmark/orders_2__t40_orders_2.p',t2_subset)).

fof(f149,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK2(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f99,f74,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox2/benchmark/orders_2__t40_orders_2.p',t5_subset)).

fof(f143,plain,
    ( ~ spl4_13
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f62,f116,f141])).

fof(f116,plain,
    ( spl4_9
  <=> ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f62,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(sK1,sK0) )
    & r2_wellord1(u1_orders_2(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X1,X0) )
            & r2_wellord1(u1_orders_2(X0),X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v6_orders_2(X1,sK0) )
          & r2_wellord1(u1_orders_2(sK0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r2_wellord1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v6_orders_2(sK1,X0) )
        & r2_wellord1(u1_orders_2(X0),sK1)
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r2_wellord1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X1,X0) )
          & r2_wellord1(u1_orders_2(X0),X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_wellord1(u1_orders_2(X0),X1)
             => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_wellord1(u1_orders_2(X0),X1)
           => ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t40_orders_2.p',t40_orders_2)).

fof(f131,plain,
    ( spl4_10
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f122,f98,f129])).

fof(f129,plain,
    ( spl4_10
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f121,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f60,f119])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f114,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f61,f112])).

fof(f61,plain,(
    r2_wellord1(u1_orders_2(sK0),sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f107,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f86,f105])).

fof(f86,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    l1_orders_2(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f57])).

fof(f57,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK3) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t40_orders_2.p',existence_l1_orders_2)).

fof(f100,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f63,f98])).

fof(f63,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t40_orders_2.p',dt_o_0_0_xboole_0)).

fof(f93,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f59,f91])).

fof(f59,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
