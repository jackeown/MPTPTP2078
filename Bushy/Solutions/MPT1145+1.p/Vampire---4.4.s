%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t37_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:20 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 345 expanded)
%              Number of leaves         :   41 ( 145 expanded)
%              Depth                    :    9
%              Number of atoms          :  421 (1127 expanded)
%              Number of equality atoms :    9 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f93,f100,f107,f114,f121,f128,f138,f151,f159,f167,f179,f192,f213,f222,f230,f241,f250,f257,f272,f281,f289,f298,f307,f309,f311,f313,f315,f319])).

fof(f319,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | spl5_23
    | ~ spl5_44 ),
    inference(avatar_contradiction_clause,[],[f318])).

fof(f318,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_23
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f317,f85])).

fof(f85,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_0
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f317,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl5_12
    | ~ spl5_23
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f316,f127])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl5_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f316,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl5_23
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f306,f297])).

fof(f297,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK2)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl5_44
  <=> r7_relat_2(u1_orders_2(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f306,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ spl5_23 ),
    inference(resolution,[],[f65,f178])).

fof(f178,plain,
    ( ~ v6_orders_2(sK2,sK0)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl5_23
  <=> ~ v6_orders_2(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v6_orders_2(X1,X0)
      | ~ r7_relat_2(u1_orders_2(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t37_orders_2.p',d11_orders_2)).

fof(f315,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | spl5_23
    | ~ spl5_44 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_23
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f300,f127])).

fof(f300,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_23
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f85,f178,f297,f65])).

fof(f313,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | spl5_23
    | ~ spl5_44 ),
    inference(avatar_contradiction_clause,[],[f312])).

fof(f312,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_23
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f302,f297])).

fof(f302,plain,
    ( ~ r7_relat_2(u1_orders_2(sK0),sK2)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_23 ),
    inference(unit_resulting_resolution,[],[f85,f178,f127,f65])).

fof(f311,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | spl5_23
    | ~ spl5_44 ),
    inference(avatar_contradiction_clause,[],[f310])).

fof(f310,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_23
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f303,f178])).

fof(f303,plain,
    ( v6_orders_2(sK2,sK0)
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f85,f297,f127,f65])).

fof(f309,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | spl5_23
    | ~ spl5_44 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_23
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f304,f85])).

fof(f304,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl5_12
    | ~ spl5_23
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f178,f297,f127,f65])).

fof(f307,plain,
    ( ~ spl5_0
    | ~ spl5_12
    | spl5_23
    | ~ spl5_44 ),
    inference(avatar_contradiction_clause,[],[f305])).

fof(f305,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_12
    | ~ spl5_23
    | ~ spl5_44 ),
    inference(unit_resulting_resolution,[],[f85,f178,f297,f127,f65])).

fof(f298,plain,
    ( spl5_44
    | ~ spl5_8
    | ~ spl5_34
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f290,f287,f248,f112,f296])).

fof(f112,plain,
    ( spl5_8
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f248,plain,
    ( spl5_34
  <=> v1_relat_1(u1_orders_2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f287,plain,
    ( spl5_42
  <=> r7_relat_2(u1_orders_2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f290,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK2)
    | ~ spl5_8
    | ~ spl5_34
    | ~ spl5_42 ),
    inference(unit_resulting_resolution,[],[f113,f249,f288,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r7_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r7_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( r7_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r7_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( r7_relat_2(X2,X1)
      | ~ r1_tarski(X1,X0)
      | ~ r7_relat_2(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(X1,X0)
          & r7_relat_2(X2,X0) )
       => r7_relat_2(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t37_orders_2.p',t96_orders_1)).

fof(f288,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f287])).

fof(f249,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f248])).

fof(f113,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f112])).

fof(f289,plain,
    ( spl5_42
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f282,f119,f105,f84,f287])).

fof(f105,plain,
    ( spl5_6
  <=> v6_orders_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f119,plain,
    ( spl5_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f282,plain,
    ( r7_relat_2(u1_orders_2(sK0),sK1)
    | ~ spl5_0
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f85,f106,f120,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r7_relat_2(u1_orders_2(X0),X1)
      | ~ v6_orders_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f120,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f106,plain,
    ( v6_orders_2(sK1,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f281,plain,
    ( spl5_40
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f273,f270,f279])).

fof(f279,plain,
    ( spl5_40
  <=> v1_relat_1(u1_orders_2(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f270,plain,
    ( spl5_38
  <=> m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f273,plain,
    ( v1_relat_1(u1_orders_2(sK4))
    | ~ spl5_38 ),
    inference(unit_resulting_resolution,[],[f271,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t37_orders_2.p',cc1_relset_1)).

fof(f271,plain,
    ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f270])).

fof(f272,plain,
    ( spl5_38
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f234,f98,f270])).

fof(f98,plain,
    ( spl5_4
  <=> l1_orders_2(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f234,plain,
    ( m1_subset_1(u1_orders_2(sK4),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK4),u1_struct_0(sK4))))
    | ~ spl5_4 ),
    inference(unit_resulting_resolution,[],[f99,f63])).

fof(f63,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t37_orders_2.p',dt_u1_orders_2)).

fof(f99,plain,
    ( l1_orders_2(sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f257,plain,
    ( spl5_36
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f243,f239,f255])).

fof(f255,plain,
    ( spl5_36
  <=> r1_tarski(u1_orders_2(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f239,plain,
    ( spl5_32
  <=> m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f243,plain,
    ( r1_tarski(u1_orders_2(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f240,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t37_orders_2.p',t3_subset)).

fof(f240,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f239])).

fof(f250,plain,
    ( spl5_34
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f242,f239,f248])).

fof(f242,plain,
    ( v1_relat_1(u1_orders_2(sK0))
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f240,f76])).

fof(f241,plain,
    ( spl5_32
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f233,f84,f239])).

fof(f233,plain,
    ( m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl5_0 ),
    inference(unit_resulting_resolution,[],[f85,f63])).

fof(f230,plain,
    ( spl5_30
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f215,f211,f228])).

fof(f228,plain,
    ( spl5_30
  <=> m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f211,plain,
    ( spl5_26
  <=> o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f215,plain,
    ( m1_subset_1(o_0_0_xboole_0,k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_26 ),
    inference(superposition,[],[f67,f212])).

fof(f212,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f211])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t37_orders_2.p',existence_m1_subset_1)).

fof(f222,plain,
    ( spl5_28
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f214,f211,f220])).

fof(f220,plain,
    ( spl5_28
  <=> r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f214,plain,
    ( r1_tarski(o_0_0_xboole_0,o_0_0_xboole_0)
    | ~ spl5_26 ),
    inference(superposition,[],[f142,f212])).

fof(f142,plain,(
    ! [X0] : r1_tarski(sK3(k1_zfmisc_1(X0)),X0) ),
    inference(unit_resulting_resolution,[],[f67,f71])).

fof(f213,plain,
    ( spl5_26
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f198,f190,f91,f211])).

fof(f91,plain,
    ( spl5_2
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f190,plain,
    ( spl5_24
  <=> v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f198,plain,
    ( o_0_0_xboole_0 = sK3(k1_zfmisc_1(o_0_0_xboole_0))
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(unit_resulting_resolution,[],[f191,f131])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | o_0_0_xboole_0 = X0 )
    | ~ spl5_2 ),
    inference(backward_demodulation,[],[f129,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t37_orders_2.p',t6_boole)).

fof(f129,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f92,f66])).

fof(f92,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f191,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f190])).

fof(f192,plain,
    ( spl5_24
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f185,f91,f190])).

fof(f185,plain,
    ( v1_xboole_0(sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f67,f184,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t37_orders_2.p',t2_subset)).

fof(f184,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK3(k1_zfmisc_1(o_0_0_xboole_0)))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f92,f67,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t37_orders_2.p',t5_subset)).

fof(f179,plain,
    ( ~ spl5_23
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f61,f123,f177])).

fof(f123,plain,
    ( spl5_13
  <=> ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f61,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(sK2,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(sK2,sK0) )
    & r1_tarski(sK2,sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v6_orders_2(sK1,sK0)
    & l1_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f48,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(X2,X0) )
                & r1_tarski(X2,X1)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
        & l1_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
                | ~ v6_orders_2(X2,sK0) )
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v6_orders_2(X1,sK0) )
      & l1_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(X2,X0) )
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
     => ( ? [X2] :
            ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
            & r1_tarski(X2,sK1)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        & v6_orders_2(sK1,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v6_orders_2(X2,X0) )
          & r1_tarski(X2,X1)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v6_orders_2(sK2,X0) )
        & r1_tarski(sK2,X1)
        & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(X2,X0) )
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(X2,X0) )
              & r1_tarski(X2,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X1,X0) )
      & l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( l1_orders_2(X0)
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v6_orders_2(X1,X0) )
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(X2,X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X1,X0) )
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,X1)
               => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t37_orders_2.p',t37_orders_2)).

fof(f167,plain,
    ( spl5_20
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f152,f112,f165])).

fof(f165,plain,
    ( spl5_20
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f152,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl5_8 ),
    inference(unit_resulting_resolution,[],[f113,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f159,plain,
    ( spl5_18
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f144,f126,f157])).

fof(f157,plain,
    ( spl5_18
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f144,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl5_12 ),
    inference(unit_resulting_resolution,[],[f127,f71])).

fof(f151,plain,
    ( spl5_16
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f143,f119,f149])).

fof(f149,plain,
    ( spl5_16
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f143,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f120,f71])).

fof(f138,plain,
    ( spl5_14
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f129,f91,f136])).

fof(f136,plain,
    ( spl5_14
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f128,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f59,f126])).

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f121,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f58,f119])).

fof(f58,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f114,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f60,f112])).

fof(f60,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f107,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f57,f105])).

fof(f57,plain,(
    v6_orders_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f79,f98])).

fof(f79,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    l1_orders_2(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f14,f54])).

fof(f54,plain,
    ( ? [X0] : l1_orders_2(X0)
   => l1_orders_2(sK4) ),
    introduced(choice_axiom,[])).

fof(f14,axiom,(
    ? [X0] : l1_orders_2(X0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t37_orders_2.p',existence_l1_orders_2)).

fof(f93,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f62,f91])).

fof(f62,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t37_orders_2.p',dt_o_0_0_xboole_0)).

fof(f86,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f56,f84])).

fof(f56,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
