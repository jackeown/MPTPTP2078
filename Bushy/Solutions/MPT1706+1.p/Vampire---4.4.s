%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t15_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:11 EDT 2019

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 319 expanded)
%              Number of leaves         :   36 ( 119 expanded)
%              Depth                    :   15
%              Number of atoms          :  457 (1275 expanded)
%              Number of equality atoms :   12 (  52 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f290,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f85,f92,f99,f106,f113,f120,f127,f134,f141,f148,f155,f174,f193,f205,f223,f236,f246,f250,f267,f274,f286,f289])).

fof(f289,plain,
    ( ~ spl7_26
    | spl7_45 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | ~ spl7_26
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f287,f192])).

fof(f192,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f191])).

fof(f191,plain,
    ( spl7_26
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f287,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ spl7_45 ),
    inference(resolution,[],[f285,f70])).

fof(f70,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t15_tmap_1.p',dt_l1_pre_topc)).

fof(f285,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl7_45
  <=> ~ l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f286,plain,
    ( ~ spl7_45
    | spl7_3
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f254,f231,f83,f284])).

fof(f83,plain,
    ( spl7_3
  <=> ~ v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f231,plain,
    ( spl7_38
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f254,plain,
    ( ~ l1_struct_0(sK1)
    | ~ spl7_3
    | ~ spl7_38 ),
    inference(subsumption_resolution,[],[f251,f84])).

fof(f84,plain,
    ( ~ v2_struct_0(sK1)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f251,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_38 ),
    inference(resolution,[],[f232,f66])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t15_tmap_1.p',fc2_struct_0)).

fof(f232,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f231])).

fof(f274,plain,
    ( spl7_42
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f256,f231,f272])).

fof(f272,plain,
    ( spl7_42
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f256,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl7_38 ),
    inference(backward_demodulation,[],[f253,f232])).

fof(f253,plain,
    ( u1_struct_0(sK1) = k1_xboole_0
    | ~ spl7_38 ),
    inference(resolution,[],[f232,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t15_tmap_1.p',t6_boole)).

fof(f267,plain,
    ( spl7_40
    | ~ spl7_16
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f260,f231,f132,f265])).

fof(f265,plain,
    ( spl7_40
  <=> m1_subset_1(sK3,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f132,plain,
    ( spl7_16
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f260,plain,
    ( m1_subset_1(sK3,k1_xboole_0)
    | ~ spl7_16
    | ~ spl7_38 ),
    inference(backward_demodulation,[],[f253,f133])).

fof(f133,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f132])).

fof(f250,plain,
    ( spl7_38
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | spl7_19 ),
    inference(avatar_split_clause,[],[f247,f139,f132,f125,f118,f111,f104,f97,f231])).

fof(f97,plain,
    ( spl7_6
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f104,plain,
    ( spl7_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f111,plain,
    ( spl7_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f118,plain,
    ( spl7_12
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f125,plain,
    ( spl7_14
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f139,plain,
    ( spl7_19
  <=> ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f247,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f243,f140])).

fof(f140,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f139])).

fof(f243,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f242,f126])).

fof(f126,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl7_14 ),
    inference(avatar_component_clause,[],[f125])).

fof(f242,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v1_xboole_0(u1_struct_0(sK1))
    | m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_16 ),
    inference(subsumption_resolution,[],[f240,f119])).

fof(f119,plain,
    ( m1_pre_topc(sK1,sK2)
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f240,plain,
    ( ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v1_xboole_0(u1_struct_0(sK1))
    | m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_16 ),
    inference(resolution,[],[f237,f133])).

fof(f237,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(X1))
        | ~ m1_pre_topc(X1,sK2)
        | ~ m1_pre_topc(X1,sK0)
        | v1_xboole_0(u1_struct_0(X1))
        | m1_subset_1(X0,u1_struct_0(sK2)) )
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(resolution,[],[f212,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t15_tmap_1.p',t2_subset)).

fof(f212,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,u1_struct_0(X3))
        | m1_subset_1(X2,u1_struct_0(sK2))
        | ~ m1_pre_topc(X3,sK2)
        | ~ m1_pre_topc(X3,sK0) )
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(resolution,[],[f176,f183])).

fof(f183,plain,
    ( ! [X0] :
        ( r1_tarski(u1_struct_0(X0),u1_struct_0(sK2))
        | ~ m1_pre_topc(X0,sK2)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f182,f98])).

fof(f98,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f182,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK2)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) )
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f177,f105])).

fof(f105,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f177,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK2)
        | r1_tarski(u1_struct_0(X0),u1_struct_0(sK2)) )
    | ~ spl7_10 ),
    inference(resolution,[],[f64,f112])).

fof(f112,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t15_tmap_1.p',t4_tsep_1)).

fof(f176,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X4)
      | m1_subset_1(X2,X4)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f58,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t15_tmap_1.p',t3_subset)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t15_tmap_1.p',t4_subset)).

fof(f246,plain,
    ( ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | spl7_19
    | spl7_39 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_19
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f244,f140])).

fof(f244,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12
    | ~ spl7_14
    | ~ spl7_16
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f243,f235])).

fof(f235,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl7_39
  <=> ~ v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f236,plain,
    ( spl7_36
    | ~ spl7_39
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(avatar_split_clause,[],[f209,f125,f104,f97,f234,f228])).

fof(f228,plain,
    ( spl7_36
  <=> ! [X5,X4] :
        ( ~ r2_hidden(X4,u1_struct_0(X5))
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_36])])).

fof(f209,plain,
    ( ! [X4,X5] :
        ( ~ v1_xboole_0(u1_struct_0(sK1))
        | ~ r2_hidden(X4,u1_struct_0(X5))
        | ~ m1_pre_topc(X5,sK1)
        | ~ m1_pre_topc(X5,sK0) )
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(resolution,[],[f167,f186])).

fof(f186,plain,
    ( ! [X2] :
        ( r1_tarski(u1_struct_0(X2),u1_struct_0(sK1))
        | ~ m1_pre_topc(X2,sK1)
        | ~ m1_pre_topc(X2,sK0) )
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f185,f98])).

fof(f185,plain,
    ( ! [X2] :
        ( ~ m1_pre_topc(X2,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK1)
        | r1_tarski(u1_struct_0(X2),u1_struct_0(sK1)) )
    | ~ spl7_8
    | ~ spl7_14 ),
    inference(subsumption_resolution,[],[f179,f105])).

fof(f179,plain,
    ( ! [X2] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X2,sK1)
        | r1_tarski(u1_struct_0(X2),u1_struct_0(sK1)) )
    | ~ spl7_14 ),
    inference(resolution,[],[f64,f126])).

fof(f167,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X3,X4)
      | ~ v1_xboole_0(X4)
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f57,f59])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/tmap_1__t15_tmap_1.p',t5_subset)).

fof(f223,plain,
    ( spl7_32
    | ~ spl7_35
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f208,f111,f104,f97,f221,f215])).

fof(f215,plain,
    ( spl7_32
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,u1_struct_0(X3))
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f221,plain,
    ( spl7_35
  <=> ~ v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_35])])).

fof(f208,plain,
    ( ! [X2,X3] :
        ( ~ v1_xboole_0(u1_struct_0(sK2))
        | ~ r2_hidden(X2,u1_struct_0(X3))
        | ~ m1_pre_topc(X3,sK2)
        | ~ m1_pre_topc(X3,sK0) )
    | ~ spl7_6
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(resolution,[],[f167,f183])).

fof(f205,plain,
    ( ~ spl7_29
    | spl7_30
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f184,f172,f118,f203,f200])).

fof(f200,plain,
    ( spl7_29
  <=> ~ v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_29])])).

fof(f203,plain,
    ( spl7_30
  <=> ! [X1] :
        ( ~ m1_pre_topc(X1,sK2)
        | r1_tarski(u1_struct_0(X1),u1_struct_0(sK1))
        | ~ m1_pre_topc(X1,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_30])])).

fof(f172,plain,
    ( spl7_24
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f184,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK2)
        | ~ v2_pre_topc(sK2)
        | ~ m1_pre_topc(X1,sK1)
        | r1_tarski(u1_struct_0(X1),u1_struct_0(sK1)) )
    | ~ spl7_12
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f178,f173])).

fof(f173,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f172])).

fof(f178,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK2)
        | ~ m1_pre_topc(X1,sK2)
        | ~ v2_pre_topc(sK2)
        | ~ m1_pre_topc(X1,sK1)
        | r1_tarski(u1_struct_0(X1),u1_struct_0(sK1)) )
    | ~ spl7_12 ),
    inference(resolution,[],[f64,f119])).

fof(f193,plain,
    ( spl7_26
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f164,f118,f111,f104,f191])).

fof(f164,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_8
    | ~ spl7_10
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f159,f163])).

fof(f163,plain,
    ( l1_pre_topc(sK2)
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(subsumption_resolution,[],[f158,f105])).

fof(f158,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f68,f112])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t15_tmap_1.p',dt_m1_pre_topc)).

fof(f159,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK1)
    | ~ spl7_12 ),
    inference(resolution,[],[f68,f119])).

fof(f174,plain,
    ( spl7_24
    | ~ spl7_8
    | ~ spl7_10 ),
    inference(avatar_split_clause,[],[f163,f111,f104,f172])).

fof(f155,plain,(
    spl7_22 ),
    inference(avatar_split_clause,[],[f56,f153])).

fof(f153,plain,
    ( spl7_22
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f56,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t15_tmap_1.p',d2_xboole_0)).

fof(f148,plain,(
    spl7_20 ),
    inference(avatar_split_clause,[],[f69,f146])).

fof(f146,plain,
    ( spl7_20
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f69,plain,(
    l1_pre_topc(sK6) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ? [X0] : l1_pre_topc(X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t15_tmap_1.p',existence_l1_pre_topc)).

fof(f141,plain,(
    ~ spl7_19 ),
    inference(avatar_split_clause,[],[f71,f139])).

fof(f71,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & m1_subset_1(X3,u1_struct_0(X1)) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X1))
                     => ? [X4] :
                          ( X3 = X4
                          & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X1))
                   => ? [X4] :
                        ( X3 = X4
                        & m1_subset_1(X4,u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t15_tmap_1.p',t15_tmap_1)).

fof(f134,plain,(
    spl7_16 ),
    inference(avatar_split_clause,[],[f45,f132])).

fof(f45,plain,(
    m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f127,plain,(
    spl7_14 ),
    inference(avatar_split_clause,[],[f50,f125])).

fof(f50,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f120,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f48,f118])).

fof(f48,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f113,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f47,f111])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f106,plain,(
    spl7_8 ),
    inference(avatar_split_clause,[],[f53,f104])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f99,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f52,f97])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f92,plain,(
    ~ spl7_5 ),
    inference(avatar_split_clause,[],[f51,f90])).

fof(f90,plain,
    ( spl7_5
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f49,f83])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f78,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f46,f76])).

fof(f76,plain,
    ( spl7_1
  <=> ~ v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f46,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
