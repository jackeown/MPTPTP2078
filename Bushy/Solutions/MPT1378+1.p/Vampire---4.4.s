%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t3_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:53 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 316 expanded)
%              Number of leaves         :   33 ( 123 expanded)
%              Depth                    :   12
%              Number of atoms          :  511 (1054 expanded)
%              Number of equality atoms :   18 (  43 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4969,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f118,f122,f126,f134,f145,f149,f187,f209,f217,f347,f504,f512,f572,f583,f1153,f4840,f4856,f4881,f4895,f4948,f4968])).

fof(f4968,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_70
    | spl9_79
    | ~ spl9_372 ),
    inference(avatar_contradiction_clause,[],[f4967])).

fof(f4967,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_70
    | ~ spl9_79
    | ~ spl9_372 ),
    inference(subsumption_resolution,[],[f4966,f582])).

fof(f582,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_79 ),
    inference(avatar_component_clause,[],[f581])).

fof(f581,plain,
    ( spl9_79
  <=> ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_79])])).

fof(f4966,plain,
    ( m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_70
    | ~ spl9_372 ),
    inference(subsumption_resolution,[],[f4965,f113])).

fof(f113,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f112])).

fof(f112,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f4965,plain,
    ( v2_struct_0(sK0)
    | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_70
    | ~ spl9_372 ),
    inference(subsumption_resolution,[],[f4964,f511])).

fof(f511,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_70 ),
    inference(avatar_component_clause,[],[f510])).

fof(f510,plain,
    ( spl9_70
  <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_70])])).

fof(f4964,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_372 ),
    inference(subsumption_resolution,[],[f4963,f133])).

fof(f133,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl9_10
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f4963,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_372 ),
    inference(subsumption_resolution,[],[f4962,f121])).

fof(f121,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl9_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f4962,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_2
    | ~ spl9_372 ),
    inference(subsumption_resolution,[],[f4954,f117])).

fof(f117,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl9_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f4954,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_372 ),
    inference(resolution,[],[f4947,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t3_connsp_2.p',d1_connsp_2)).

fof(f4947,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl9_372 ),
    inference(avatar_component_clause,[],[f4946])).

fof(f4946,plain,
    ( spl9_372
  <=> r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_372])])).

fof(f4948,plain,
    ( spl9_372
    | spl9_363
    | ~ spl9_368 ),
    inference(avatar_split_clause,[],[f4901,f4893,f4879,f4946])).

fof(f4879,plain,
    ( spl9_363
  <=> ~ v1_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_363])])).

fof(f4893,plain,
    ( spl9_368
  <=> m1_subset_1(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_368])])).

fof(f4901,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl9_363
    | ~ spl9_368 ),
    inference(subsumption_resolution,[],[f4900,f4880])).

fof(f4880,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl9_363 ),
    inference(avatar_component_clause,[],[f4879])).

fof(f4900,plain,
    ( v1_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | r2_hidden(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl9_368 ),
    inference(resolution,[],[f4894,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t3_connsp_2.p',t2_subset)).

fof(f4894,plain,
    ( m1_subset_1(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl9_368 ),
    inference(avatar_component_clause,[],[f4893])).

fof(f4895,plain,
    ( spl9_368
    | ~ spl9_48
    | ~ spl9_360 ),
    inference(avatar_split_clause,[],[f4869,f4854,f345,f4893])).

fof(f345,plain,
    ( spl9_48
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_48])])).

fof(f4854,plain,
    ( spl9_360
  <=> m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_360])])).

fof(f4869,plain,
    ( m1_subset_1(sK1,k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl9_48
    | ~ spl9_360 ),
    inference(resolution,[],[f4855,f803])).

fof(f803,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),X1),k1_zfmisc_1(X2))
        | m1_subset_1(sK1,X2) )
    | ~ spl9_48 ),
    inference(resolution,[],[f574,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t3_connsp_2.p',t4_subset)).

fof(f574,plain,
    ( ! [X1] : r2_hidden(sK1,k2_xboole_0(k1_tops_1(sK0,sK2),X1))
    | ~ spl9_48 ),
    inference(resolution,[],[f392,f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t3_connsp_2.p',d3_xboole_0)).

fof(f392,plain,
    ( ! [X1] : sP8(sK1,X1,k1_tops_1(sK0,sK2))
    | ~ spl9_48 ),
    inference(resolution,[],[f346,f91])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f346,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl9_48 ),
    inference(avatar_component_clause,[],[f345])).

fof(f4855,plain,
    ( m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK3))))
    | ~ spl9_360 ),
    inference(avatar_component_clause,[],[f4854])).

fof(f4881,plain,
    ( ~ spl9_363
    | ~ spl9_48
    | ~ spl9_360 ),
    inference(avatar_split_clause,[],[f4870,f4854,f345,f4879])).

fof(f4870,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl9_48
    | ~ spl9_360 ),
    inference(resolution,[],[f4855,f806])).

fof(f806,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),X7),k1_zfmisc_1(X8))
        | ~ v1_xboole_0(X8) )
    | ~ spl9_48 ),
    inference(resolution,[],[f574,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t3_connsp_2.p',t5_subset)).

fof(f4856,plain,
    ( spl9_360
    | ~ spl9_26
    | ~ spl9_30
    | ~ spl9_358 ),
    inference(avatar_split_clause,[],[f4841,f4838,f215,f207,f4854])).

fof(f207,plain,
    ( spl9_26
  <=> m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f215,plain,
    ( spl9_30
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_30])])).

fof(f4838,plain,
    ( spl9_358
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_358])])).

fof(f4841,plain,
    ( m1_subset_1(k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK3))))
    | ~ spl9_26
    | ~ spl9_30
    | ~ spl9_358 ),
    inference(forward_demodulation,[],[f4839,f1323])).

fof(f1323,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(forward_demodulation,[],[f1315,f99])).

fof(f99,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t3_connsp_2.p',commutativity_k2_xboole_0)).

fof(f1315,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k2_xboole_0(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl9_26
    | ~ spl9_30 ),
    inference(resolution,[],[f224,f216])).

fof(f216,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_30 ),
    inference(avatar_component_clause,[],[f215])).

fof(f224,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),X3) = k2_xboole_0(k1_tops_1(sK0,sK3),X3) )
    | ~ spl9_26 ),
    inference(resolution,[],[f208,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t3_connsp_2.p',redefinition_k4_subset_1)).

fof(f208,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f207])).

fof(f4839,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK3))))
    | ~ spl9_358 ),
    inference(avatar_component_clause,[],[f4838])).

fof(f4840,plain,
    ( spl9_358
    | ~ spl9_144 ),
    inference(avatar_split_clause,[],[f1197,f1151,f4838])).

fof(f1151,plain,
    ( spl9_144
  <=> r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_144])])).

fof(f1197,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)),k1_zfmisc_1(k1_tops_1(sK0,k2_xboole_0(sK2,sK3))))
    | ~ spl9_144 ),
    inference(resolution,[],[f1152,f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t3_connsp_2.p',t3_subset)).

fof(f1152,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl9_144 ),
    inference(avatar_component_clause,[],[f1151])).

fof(f1153,plain,
    ( spl9_144
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f408,f147,f143,f120,f1151])).

fof(f143,plain,
    ( spl9_12
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f147,plain,
    ( spl9_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f408,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k2_xboole_0(sK2,sK3)))
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_14 ),
    inference(forward_demodulation,[],[f400,f342])).

fof(f342,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK3,sK2) = k2_xboole_0(sK2,sK3)
    | ~ spl9_12
    | ~ spl9_14 ),
    inference(forward_demodulation,[],[f339,f99])).

fof(f339,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK3,sK2) = k2_xboole_0(sK3,sK2)
    | ~ spl9_12
    | ~ spl9_14 ),
    inference(resolution,[],[f156,f148])).

fof(f148,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f156,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK3,X3) = k2_xboole_0(sK3,X3) )
    | ~ spl9_12 ),
    inference(resolution,[],[f144,f79])).

fof(f144,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f400,plain,
    ( r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK3,sK2)))
    | ~ spl9_4
    | ~ spl9_12
    | ~ spl9_14 ),
    inference(resolution,[],[f159,f148])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK3,X0))) )
    | ~ spl9_4
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f150,f121])).

fof(f150,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k4_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,X0)),k1_tops_1(sK0,k4_subset_1(u1_struct_0(sK0),sK3,X0))) )
    | ~ spl9_12 ),
    inference(resolution,[],[f144,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k4_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)),k1_tops_1(X0,k4_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t3_connsp_2.p',t49_tops_1)).

fof(f583,plain,
    ( ~ spl9_79
    | spl9_19
    | ~ spl9_76 ),
    inference(avatar_split_clause,[],[f579,f570,f185,f581])).

fof(f185,plain,
    ( spl9_19
  <=> ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f570,plain,
    ( spl9_76
  <=> k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_76])])).

fof(f579,plain,
    ( ~ m1_connsp_2(k2_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_19
    | ~ spl9_76 ),
    inference(superposition,[],[f186,f571])).

fof(f571,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k2_xboole_0(sK2,sK3)
    | ~ spl9_76 ),
    inference(avatar_component_clause,[],[f570])).

fof(f186,plain,
    ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f185])).

fof(f572,plain,
    ( spl9_76
    | ~ spl9_12
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f365,f147,f143,f570])).

fof(f365,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK3) = k2_xboole_0(sK2,sK3)
    | ~ spl9_12
    | ~ spl9_14 ),
    inference(resolution,[],[f171,f144])).

fof(f171,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK2,X3) = k2_xboole_0(sK2,X3) )
    | ~ spl9_14 ),
    inference(resolution,[],[f148,f79])).

fof(f512,plain,
    ( spl9_70
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f505,f502,f147,f143,f510])).

fof(f502,plain,
    ( spl9_68
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f505,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_12
    | ~ spl9_14
    | ~ spl9_68 ),
    inference(forward_demodulation,[],[f503,f342])).

fof(f503,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f502])).

fof(f504,plain,
    ( spl9_68
    | ~ spl9_12
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f329,f147,f143,f502])).

fof(f329,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_12
    | ~ spl9_14 ),
    inference(resolution,[],[f155,f148])).

fof(f155,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK3,X2),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl9_12 ),
    inference(resolution,[],[f144,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t3_connsp_2.p',dt_k4_subset_1)).

fof(f347,plain,
    ( spl9_48
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f323,f147,f132,f124,f120,f116,f112,f345])).

fof(f124,plain,
    ( spl9_6
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f323,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f322,f133])).

fof(f322,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_14 ),
    inference(resolution,[],[f179,f125])).

fof(f125,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f179,plain,
    ( ! [X1] :
        ( ~ m1_connsp_2(sK2,sK0,X1)
        | r2_hidden(X1,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f178,f113])).

fof(f178,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X1,k1_tops_1(sK0,sK2))
        | ~ m1_connsp_2(sK2,sK0,X1) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f177,f121])).

fof(f177,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X1,k1_tops_1(sK0,sK2))
        | ~ m1_connsp_2(sK2,sK0,X1) )
    | ~ spl9_2
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f168,f117])).

fof(f168,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X1,k1_tops_1(sK0,sK2))
        | ~ m1_connsp_2(sK2,sK0,X1) )
    | ~ spl9_14 ),
    inference(resolution,[],[f148,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f217,plain,
    ( spl9_30
    | ~ spl9_4
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f175,f147,f120,f215])).

fof(f175,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f166,f121])).

fof(f166,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_14 ),
    inference(resolution,[],[f148,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t3_connsp_2.p',dt_k1_tops_1)).

fof(f209,plain,
    ( spl9_26
    | ~ spl9_4
    | ~ spl9_12 ),
    inference(avatar_split_clause,[],[f160,f143,f120,f207])).

fof(f160,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_12 ),
    inference(subsumption_resolution,[],[f151,f121])).

fof(f151,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_12 ),
    inference(resolution,[],[f144,f89])).

fof(f187,plain,(
    ~ spl9_19 ),
    inference(avatar_split_clause,[],[f72,f185])).

fof(f72,plain,(
    ~ m1_connsp_2(k4_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                  & m1_connsp_2(X3,X0,X1)
                  & m1_connsp_2(X2,X0,X1)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                     => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                   => m1_connsp_2(k4_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t3_connsp_2.p',t3_connsp_2)).

fof(f149,plain,(
    spl9_14 ),
    inference(avatar_split_clause,[],[f73,f147])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f145,plain,(
    spl9_12 ),
    inference(avatar_split_clause,[],[f69,f143])).

fof(f69,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f134,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f74,f132])).

fof(f74,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f39])).

fof(f126,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f70,f124])).

fof(f70,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f39])).

fof(f122,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f77,f120])).

fof(f77,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f118,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f76,f116])).

fof(f76,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f114,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f75,f112])).

fof(f75,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
