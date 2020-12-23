%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 423 expanded)
%              Number of leaves         :   28 ( 175 expanded)
%              Depth                    :   12
%              Number of atoms          :  704 (1615 expanded)
%              Number of equality atoms :   26 (  77 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (1696)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
fof(f591,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f77,f81,f135,f139,f143,f147,f163,f171,f178,f186,f202,f207,f298,f414,f419,f556,f590])).

fof(f590,plain,
    ( spl7_8
    | ~ spl7_52 ),
    inference(avatar_contradiction_clause,[],[f589])).

fof(f589,plain,
    ( $false
    | spl7_8
    | ~ spl7_52 ),
    inference(subsumption_resolution,[],[f585,f134])).

fof(f134,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl7_8
  <=> m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f585,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl7_52 ),
    inference(resolution,[],[f555,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f555,plain,
    ( r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f554])).

fof(f554,plain,
    ( spl7_52
  <=> r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f556,plain,
    ( spl7_52
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_28
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f431,f417,f296,f141,f67,f63,f59,f55,f554])).

fof(f55,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f59,plain,
    ( spl7_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f63,plain,
    ( spl7_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f67,plain,
    ( spl7_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f141,plain,
    ( spl7_10
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f296,plain,
    ( spl7_28
  <=> v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f417,plain,
    ( spl7_39
  <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f431,plain,
    ( r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_28
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f430,f297])).

fof(f297,plain,
    ( v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f296])).

fof(f430,plain,
    ( ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_10
    | ~ spl7_39 ),
    inference(subsumption_resolution,[],[f420,f188])).

fof(f188,plain,
    ( ! [X1] : r2_hidden(sK1,k2_xboole_0(sK2,X1))
    | ~ spl7_10 ),
    inference(resolution,[],[f154,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f154,plain,
    ( ! [X1] : sP5(sK1,X1,sK2)
    | ~ spl7_10 ),
    inference(resolution,[],[f142,f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f142,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f141])).

fof(f420,plain,
    ( ~ r2_hidden(sK1,k2_xboole_0(sK2,sK3))
    | ~ v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_39 ),
    inference(resolution,[],[f418,f73])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X0)
        | ~ v3_pre_topc(X0,sK0)
        | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK0,sK1))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f72,f56])).

fof(f56,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f72,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X0)
        | ~ v3_pre_topc(X0,sK0)
        | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK0,sK1))) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f71,f64])).

fof(f64,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f71,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X0)
        | ~ v3_pre_topc(X0,sK0)
        | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK0,sK1))) )
    | ~ spl7_2
    | ~ spl7_4 ),
    inference(subsumption_resolution,[],[f70,f60])).

fof(f60,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X0)
        | ~ v3_pre_topc(X0,sK0)
        | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK0,sK1))) )
    | ~ spl7_4 ),
    inference(resolution,[],[f68,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ v3_pre_topc(X2,X0)
      | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f68,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f418,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f417])).

fof(f419,plain,
    ( spl7_39
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_38 ),
    inference(avatar_split_clause,[],[f415,f412,f205,f184,f417])).

fof(f184,plain,
    ( spl7_17
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f205,plain,
    ( spl7_19
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f412,plain,
    ( spl7_38
  <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).

fof(f415,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_38 ),
    inference(forward_demodulation,[],[f413,f305])).

fof(f305,plain,
    ( k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),sK2,sK3)
    | ~ spl7_17
    | ~ spl7_19 ),
    inference(resolution,[],[f210,f185])).

% (1697)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f185,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f184])).

fof(f210,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2) )
    | ~ spl7_19 ),
    inference(resolution,[],[f206,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f206,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f205])).

fof(f413,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_38 ),
    inference(avatar_component_clause,[],[f412])).

fof(f414,plain,
    ( spl7_38
    | ~ spl7_17
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f299,f205,f184,f412])).

fof(f299,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_17
    | ~ spl7_19 ),
    inference(resolution,[],[f209,f185])).

fof(f209,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,X1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_19 ),
    inference(resolution,[],[f206,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f298,plain,
    ( spl7_28
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_17
    | ~ spl7_19 ),
    inference(avatar_split_clause,[],[f285,f205,f184,f145,f137,f63,f59,f296])).

fof(f137,plain,
    ( spl7_9
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f145,plain,
    ( spl7_11
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f285,plain,
    ( v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_9
    | ~ spl7_11
    | ~ spl7_17
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f283,f138])).

fof(f138,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f137])).

fof(f283,plain,
    ( ~ v3_pre_topc(sK3,sK0)
    | v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_17
    | ~ spl7_19 ),
    inference(resolution,[],[f213,f185])).

fof(f213,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | v3_pre_topc(k2_xboole_0(sK2,X0),sK0) )
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f212,f60])).

fof(f212,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k2_xboole_0(sK2,X0),sK0) )
    | ~ spl7_3
    | ~ spl7_11
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f211,f146])).

fof(f146,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(sK2,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k2_xboole_0(sK2,X0),sK0) )
    | ~ spl7_3
    | ~ spl7_19 ),
    inference(subsumption_resolution,[],[f208,f64])).

fof(f208,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v3_pre_topc(sK2,sK0)
        | ~ v2_pre_topc(sK0)
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k2_xboole_0(sK2,X0),sK0) )
    | ~ spl7_19 ),
    inference(resolution,[],[f206,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f207,plain,
    ( spl7_19
    | ~ spl7_15
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f203,f200,f169,f205])).

fof(f169,plain,
    ( spl7_15
  <=> sK2 = sK6(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f200,plain,
    ( spl7_18
  <=> m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f203,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_15
    | ~ spl7_18 ),
    inference(forward_demodulation,[],[f201,f170])).

fof(f170,plain,
    ( sK2 = sK6(sK0,sK1,sK2)
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f201,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f200])).

fof(f202,plain,
    ( spl7_18
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f113,f79,f67,f63,f59,f55,f200])).

fof(f79,plain,
    ( spl7_6
  <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f113,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f112,f56])).

fof(f112,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f111,f68])).

fof(f111,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f110,f64])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f105,f60])).

fof(f105,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_6 ),
    inference(resolution,[],[f80,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

% (1708)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f80,plain,
    ( m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f79])).

fof(f186,plain,
    ( spl7_17
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(avatar_split_clause,[],[f179,f176,f161,f184])).

fof(f161,plain,
    ( spl7_13
  <=> sK3 = sK6(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f176,plain,
    ( spl7_16
  <=> m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f179,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_13
    | ~ spl7_16 ),
    inference(forward_demodulation,[],[f177,f162])).

fof(f162,plain,
    ( sK3 = sK6(sK0,sK1,sK3)
    | ~ spl7_13 ),
    inference(avatar_component_clause,[],[f161])).

fof(f177,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f176])).

fof(f178,plain,
    ( spl7_16
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f90,f75,f67,f63,f59,f55,f176])).

fof(f75,plain,
    ( spl7_5
  <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f90,plain,
    ( m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f89,f56])).

fof(f89,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f88,f68])).

fof(f88,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f87,f64])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f82,f60])).

fof(f82,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5 ),
    inference(resolution,[],[f76,f42])).

fof(f76,plain,
    ( m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f171,plain,
    ( spl7_15
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f117,f79,f67,f63,f59,f55,f169])).

fof(f117,plain,
    ( sK2 = sK6(sK0,sK1,sK2)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f116,f56])).

fof(f116,plain,
    ( v2_struct_0(sK0)
    | sK2 = sK6(sK0,sK1,sK2)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f115,f68])).

fof(f115,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK2 = sK6(sK0,sK1,sK2)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f114,f64])).

fof(f114,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK2 = sK6(sK0,sK1,sK2)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f106,f60])).

fof(f106,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK2 = sK6(sK0,sK1,sK2)
    | ~ spl7_6 ),
    inference(resolution,[],[f80,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | sK6(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f163,plain,
    ( spl7_13
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f94,f75,f67,f63,f59,f55,f161])).

fof(f94,plain,
    ( sK3 = sK6(sK0,sK1,sK3)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f93,f56])).

fof(f93,plain,
    ( v2_struct_0(sK0)
    | sK3 = sK6(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f92,f68])).

fof(f92,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK3 = sK6(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f91,f64])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK3 = sK6(sK0,sK1,sK3)
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f83,f60])).

fof(f83,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK3 = sK6(sK0,sK1,sK3)
    | ~ spl7_5 ),
    inference(resolution,[],[f76,f43])).

fof(f147,plain,
    ( spl7_11
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f127,f79,f67,f63,f59,f55,f145])).

fof(f127,plain,
    ( v3_pre_topc(sK2,sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f126,f117])).

fof(f126,plain,
    ( v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f125,f56])).

fof(f125,plain,
    ( v2_struct_0(sK0)
    | v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f124,f68])).

% (1709)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f124,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f123,f64])).

fof(f123,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f108,f60])).

fof(f108,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK6(sK0,sK1,sK2),sK0)
    | ~ spl7_6 ),
    inference(resolution,[],[f80,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v3_pre_topc(sK6(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f143,plain,
    ( spl7_10
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f122,f79,f67,f63,f59,f55,f141])).

fof(f122,plain,
    ( r2_hidden(sK1,sK2)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(forward_demodulation,[],[f121,f117])).

fof(f121,plain,
    ( r2_hidden(sK1,sK6(sK0,sK1,sK2))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f120,f56])).

fof(f120,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK1,sK6(sK0,sK1,sK2))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f119,f68])).

fof(f119,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,sK6(sK0,sK1,sK2))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f118,f64])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,sK6(sK0,sK1,sK2))
    | ~ spl7_2
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f107,f60])).

fof(f107,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,sK6(sK0,sK1,sK2))
    | ~ spl7_6 ),
    inference(resolution,[],[f80,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,sK6(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f139,plain,
    ( spl7_9
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f104,f75,f67,f63,f59,f55,f137])).

fof(f104,plain,
    ( v3_pre_topc(sK3,sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(forward_demodulation,[],[f103,f94])).

fof(f103,plain,
    ( v3_pre_topc(sK6(sK0,sK1,sK3),sK0)
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f102,f56])).

fof(f102,plain,
    ( v2_struct_0(sK0)
    | v3_pre_topc(sK6(sK0,sK1,sK3),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f101,f68])).

fof(f101,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK6(sK0,sK1,sK3),sK0)
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f100,f64])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK6(sK0,sK1,sK3),sK0)
    | ~ spl7_2
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f85,f60])).

fof(f85,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK6(sK0,sK1,sK3),sK0)
    | ~ spl7_5 ),
    inference(resolution,[],[f76,f45])).

fof(f135,plain,(
    ~ spl7_8 ),
    inference(avatar_split_clause,[],[f27,f133])).

fof(f27,plain,(
    ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

fof(f81,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f28,f79])).

fof(f28,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f77,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f26,f75])).

fof(f26,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f69,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f29,f67])).

fof(f29,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f65,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f31,f59])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f57,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f30,f55])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:08:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (1702)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (1694)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (1699)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (1694)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  % (1696)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  fof(f591,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f77,f81,f135,f139,f143,f147,f163,f171,f178,f186,f202,f207,f298,f414,f419,f556,f590])).
% 0.22/0.50  fof(f590,plain,(
% 0.22/0.50    spl7_8 | ~spl7_52),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f589])).
% 0.22/0.50  fof(f589,plain,(
% 0.22/0.50    $false | (spl7_8 | ~spl7_52)),
% 0.22/0.50    inference(subsumption_resolution,[],[f585,f134])).
% 0.22/0.50  fof(f134,plain,(
% 0.22/0.50    ~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) | spl7_8),
% 0.22/0.50    inference(avatar_component_clause,[],[f133])).
% 0.22/0.50  fof(f133,plain,(
% 0.22/0.50    spl7_8 <=> m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.50  fof(f585,plain,(
% 0.22/0.50    m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl7_52),
% 0.22/0.50    inference(resolution,[],[f555,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.22/0.50    inference(ennf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).
% 0.22/0.50  fof(f555,plain,(
% 0.22/0.50    r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl7_52),
% 0.22/0.50    inference(avatar_component_clause,[],[f554])).
% 0.22/0.50  fof(f554,plain,(
% 0.22/0.50    spl7_52 <=> r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 0.22/0.50  fof(f556,plain,(
% 0.22/0.50    spl7_52 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_10 | ~spl7_28 | ~spl7_39),
% 0.22/0.50    inference(avatar_split_clause,[],[f431,f417,f296,f141,f67,f63,f59,f55,f554])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    spl7_1 <=> v2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.50  fof(f59,plain,(
% 0.22/0.50    spl7_2 <=> v2_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl7_3 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.50  fof(f67,plain,(
% 0.22/0.50    spl7_4 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.50  fof(f141,plain,(
% 0.22/0.50    spl7_10 <=> r2_hidden(sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.50  fof(f296,plain,(
% 0.22/0.50    spl7_28 <=> v3_pre_topc(k2_xboole_0(sK2,sK3),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.22/0.50  fof(f417,plain,(
% 0.22/0.50    spl7_39 <=> m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.22/0.50  fof(f431,plain,(
% 0.22/0.50    r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_10 | ~spl7_28 | ~spl7_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f430,f297])).
% 0.22/0.50  fof(f297,plain,(
% 0.22/0.50    v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | ~spl7_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f296])).
% 0.22/0.50  fof(f430,plain,(
% 0.22/0.50    ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_10 | ~spl7_39)),
% 0.22/0.50    inference(subsumption_resolution,[],[f420,f188])).
% 0.22/0.50  fof(f188,plain,(
% 0.22/0.50    ( ! [X1] : (r2_hidden(sK1,k2_xboole_0(sK2,X1))) ) | ~spl7_10),
% 0.22/0.50    inference(resolution,[],[f154,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,k2_xboole_0(X0,X1))) )),
% 0.22/0.50    inference(equality_resolution,[],[f36])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.50  fof(f154,plain,(
% 0.22/0.50    ( ! [X1] : (sP5(sK1,X1,sK2)) ) | ~spl7_10),
% 0.22/0.50    inference(resolution,[],[f142,f33])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | sP5(X3,X1,X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f142,plain,(
% 0.22/0.50    r2_hidden(sK1,sK2) | ~spl7_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f141])).
% 0.22/0.50  fof(f420,plain,(
% 0.22/0.50    ~r2_hidden(sK1,k2_xboole_0(sK2,sK3)) | ~v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | r2_hidden(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_39)),
% 0.22/0.50    inference(resolution,[],[f418,f73])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~v3_pre_topc(X0,sK0) | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK0,sK1)))) ) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f72,f56])).
% 0.22/0.50  fof(f56,plain,(
% 0.22/0.50    ~v2_struct_0(sK0) | spl7_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f55])).
% 0.22/0.50  fof(f72,plain,(
% 0.22/0.50    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~v3_pre_topc(X0,sK0) | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK0,sK1)))) ) | (~spl7_2 | ~spl7_3 | ~spl7_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f71,f64])).
% 0.22/0.50  fof(f64,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl7_3),
% 0.22/0.50    inference(avatar_component_clause,[],[f63])).
% 0.22/0.50  fof(f71,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~v3_pre_topc(X0,sK0) | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK0,sK1)))) ) | (~spl7_2 | ~spl7_4)),
% 0.22/0.50    inference(subsumption_resolution,[],[f70,f60])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    v2_pre_topc(sK0) | ~spl7_2),
% 0.22/0.50    inference(avatar_component_clause,[],[f59])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~v3_pre_topc(X0,sK0) | r2_hidden(X0,u1_struct_0(k9_yellow_6(sK0,sK1)))) ) | ~spl7_4),
% 0.22/0.50    inference(resolution,[],[f68,f48])).
% 0.22/0.50  fof(f48,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~v3_pre_topc(X2,X0) | r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl7_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f67])).
% 0.22/0.50  fof(f418,plain,(
% 0.22/0.50    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_39),
% 0.22/0.50    inference(avatar_component_clause,[],[f417])).
% 0.22/0.50  fof(f419,plain,(
% 0.22/0.50    spl7_39 | ~spl7_17 | ~spl7_19 | ~spl7_38),
% 0.22/0.50    inference(avatar_split_clause,[],[f415,f412,f205,f184,f417])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    spl7_17 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.50  fof(f205,plain,(
% 0.22/0.50    spl7_19 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.50  fof(f412,plain,(
% 0.22/0.50    spl7_38 <=> m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_38])])).
% 0.22/0.50  fof(f415,plain,(
% 0.22/0.50    m1_subset_1(k2_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_17 | ~spl7_19 | ~spl7_38)),
% 0.22/0.50    inference(forward_demodulation,[],[f413,f305])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    k2_xboole_0(sK2,sK3) = k4_subset_1(u1_struct_0(sK0),sK2,sK3) | (~spl7_17 | ~spl7_19)),
% 0.22/0.50    inference(resolution,[],[f210,f185])).
% 0.22/0.50  % (1697)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  fof(f185,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f184])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k4_subset_1(u1_struct_0(sK0),sK2,X2) = k2_xboole_0(sK2,X2)) ) | ~spl7_19),
% 0.22/0.50    inference(resolution,[],[f206,f40])).
% 0.22/0.50  fof(f40,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(flattening,[],[f13])).
% 0.22/0.50  fof(f13,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.22/0.50  fof(f206,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f205])).
% 0.22/0.50  fof(f413,plain,(
% 0.22/0.50    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f412])).
% 0.22/0.50  fof(f414,plain,(
% 0.22/0.50    spl7_38 | ~spl7_17 | ~spl7_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f299,f205,f184,f412])).
% 0.22/0.50  fof(f299,plain,(
% 0.22/0.50    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_17 | ~spl7_19)),
% 0.22/0.50    inference(resolution,[],[f209,f185])).
% 0.22/0.50  fof(f209,plain,(
% 0.22/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,X1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl7_19),
% 0.22/0.50    inference(resolution,[],[f206,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 0.22/0.50  fof(f298,plain,(
% 0.22/0.50    spl7_28 | ~spl7_2 | ~spl7_3 | ~spl7_9 | ~spl7_11 | ~spl7_17 | ~spl7_19),
% 0.22/0.50    inference(avatar_split_clause,[],[f285,f205,f184,f145,f137,f63,f59,f296])).
% 0.22/0.50  fof(f137,plain,(
% 0.22/0.50    spl7_9 <=> v3_pre_topc(sK3,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    spl7_11 <=> v3_pre_topc(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.50  fof(f285,plain,(
% 0.22/0.50    v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | (~spl7_2 | ~spl7_3 | ~spl7_9 | ~spl7_11 | ~spl7_17 | ~spl7_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f283,f138])).
% 0.22/0.50  fof(f138,plain,(
% 0.22/0.50    v3_pre_topc(sK3,sK0) | ~spl7_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f137])).
% 0.22/0.50  fof(f283,plain,(
% 0.22/0.50    ~v3_pre_topc(sK3,sK0) | v3_pre_topc(k2_xboole_0(sK2,sK3),sK0) | (~spl7_2 | ~spl7_3 | ~spl7_11 | ~spl7_17 | ~spl7_19)),
% 0.22/0.50    inference(resolution,[],[f213,f185])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | v3_pre_topc(k2_xboole_0(sK2,X0),sK0)) ) | (~spl7_2 | ~spl7_3 | ~spl7_11 | ~spl7_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f212,f60])).
% 0.22/0.50  fof(f212,plain,(
% 0.22/0.50    ( ! [X0] : (~v2_pre_topc(sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_xboole_0(sK2,X0),sK0)) ) | (~spl7_3 | ~spl7_11 | ~spl7_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f211,f146])).
% 0.22/0.50  fof(f146,plain,(
% 0.22/0.50    v3_pre_topc(sK2,sK0) | ~spl7_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f145])).
% 0.22/0.50  fof(f211,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_xboole_0(sK2,X0),sK0)) ) | (~spl7_3 | ~spl7_19)),
% 0.22/0.50    inference(subsumption_resolution,[],[f208,f64])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | ~v3_pre_topc(sK2,sK0) | ~v2_pre_topc(sK0) | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_xboole_0(sK2,X0),sK0)) ) | ~spl7_19),
% 0.22/0.50    inference(resolution,[],[f206,f41])).
% 0.22/0.50  fof(f41,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k2_xboole_0(X1,X2),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f16])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).
% 0.22/0.50  fof(f207,plain,(
% 0.22/0.50    spl7_19 | ~spl7_15 | ~spl7_18),
% 0.22/0.50    inference(avatar_split_clause,[],[f203,f200,f169,f205])).
% 0.22/0.50  fof(f169,plain,(
% 0.22/0.50    spl7_15 <=> sK2 = sK6(sK0,sK1,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    spl7_18 <=> m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.50  fof(f203,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_15 | ~spl7_18)),
% 0.22/0.50    inference(forward_demodulation,[],[f201,f170])).
% 0.22/0.50  fof(f170,plain,(
% 0.22/0.50    sK2 = sK6(sK0,sK1,sK2) | ~spl7_15),
% 0.22/0.50    inference(avatar_component_clause,[],[f169])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f200])).
% 0.22/0.50  fof(f202,plain,(
% 0.22/0.50    spl7_18 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f113,f79,f67,f63,f59,f55,f200])).
% 0.22/0.50  fof(f79,plain,(
% 0.22/0.50    spl7_6 <=> m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f112,f56])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    v2_struct_0(sK0) | m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f111,f68])).
% 0.22/0.50  fof(f111,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f110,f64])).
% 0.22/0.50  fof(f110,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_2 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f105,f60])).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(sK6(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_6),
% 0.22/0.50    inference(resolution,[],[f80,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f7])).
% 0.22/0.50  fof(f7,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).
% 0.22/0.50  % (1708)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl7_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f79])).
% 0.22/0.50  fof(f186,plain,(
% 0.22/0.50    spl7_17 | ~spl7_13 | ~spl7_16),
% 0.22/0.50    inference(avatar_split_clause,[],[f179,f176,f161,f184])).
% 0.22/0.50  fof(f161,plain,(
% 0.22/0.50    spl7_13 <=> sK3 = sK6(sK0,sK1,sK3)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.50  fof(f176,plain,(
% 0.22/0.50    spl7_16 <=> m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.50  fof(f179,plain,(
% 0.22/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_13 | ~spl7_16)),
% 0.22/0.50    inference(forward_demodulation,[],[f177,f162])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    sK3 = sK6(sK0,sK1,sK3) | ~spl7_13),
% 0.22/0.50    inference(avatar_component_clause,[],[f161])).
% 0.22/0.50  fof(f177,plain,(
% 0.22/0.50    m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_16),
% 0.22/0.50    inference(avatar_component_clause,[],[f176])).
% 0.22/0.50  fof(f178,plain,(
% 0.22/0.50    spl7_16 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f90,f75,f67,f63,f59,f55,f176])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl7_5 <=> m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f89,f56])).
% 0.22/0.50  fof(f89,plain,(
% 0.22/0.50    v2_struct_0(sK0) | m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f88,f68])).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f87,f64])).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl7_2 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f82,f60])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | m1_subset_1(sK6(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl7_5),
% 0.22/0.50    inference(resolution,[],[f76,f42])).
% 0.22/0.50  fof(f76,plain,(
% 0.22/0.50    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~spl7_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f75])).
% 0.22/0.50  fof(f171,plain,(
% 0.22/0.50    spl7_15 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f117,f79,f67,f63,f59,f55,f169])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    sK2 = sK6(sK0,sK1,sK2) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f116,f56])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    v2_struct_0(sK0) | sK2 = sK6(sK0,sK1,sK2) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f115,f68])).
% 0.22/0.50  fof(f115,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | sK2 = sK6(sK0,sK1,sK2) | (~spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f114,f64])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | sK2 = sK6(sK0,sK1,sK2) | (~spl7_2 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f106,f60])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | sK2 = sK6(sK0,sK1,sK2) | ~spl7_6),
% 0.22/0.50    inference(resolution,[],[f80,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | sK6(X0,X1,X2) = X2) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f163,plain,(
% 0.22/0.50    spl7_13 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f94,f75,f67,f63,f59,f55,f161])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    sK3 = sK6(sK0,sK1,sK3) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f93,f56])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    v2_struct_0(sK0) | sK3 = sK6(sK0,sK1,sK3) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f92,f68])).
% 0.22/0.50  fof(f92,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | sK3 = sK6(sK0,sK1,sK3) | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f91,f64])).
% 0.22/0.50  fof(f91,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | sK3 = sK6(sK0,sK1,sK3) | (~spl7_2 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f83,f60])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | sK3 = sK6(sK0,sK1,sK3) | ~spl7_5),
% 0.22/0.50    inference(resolution,[],[f76,f43])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    spl7_11 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f127,f79,f67,f63,f59,f55,f145])).
% 0.22/0.50  fof(f127,plain,(
% 0.22/0.50    v3_pre_topc(sK2,sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6)),
% 0.22/0.50    inference(forward_demodulation,[],[f126,f117])).
% 0.22/0.50  fof(f126,plain,(
% 0.22/0.50    v3_pre_topc(sK6(sK0,sK1,sK2),sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f125,f56])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    v2_struct_0(sK0) | v3_pre_topc(sK6(sK0,sK1,sK2),sK0) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f124,f68])).
% 0.22/0.50  % (1709)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  fof(f124,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v3_pre_topc(sK6(sK0,sK1,sK2),sK0) | (~spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f123,f64])).
% 0.22/0.50  fof(f123,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v3_pre_topc(sK6(sK0,sK1,sK2),sK0) | (~spl7_2 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f108,f60])).
% 0.22/0.50  fof(f108,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v3_pre_topc(sK6(sK0,sK1,sK2),sK0) | ~spl7_6),
% 0.22/0.50    inference(resolution,[],[f80,f45])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v3_pre_topc(sK6(X0,X1,X2),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f143,plain,(
% 0.22/0.50    spl7_10 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f122,f79,f67,f63,f59,f55,f141])).
% 0.22/0.50  fof(f122,plain,(
% 0.22/0.50    r2_hidden(sK1,sK2) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6)),
% 0.22/0.50    inference(forward_demodulation,[],[f121,f117])).
% 0.22/0.50  fof(f121,plain,(
% 0.22/0.50    r2_hidden(sK1,sK6(sK0,sK1,sK2)) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f120,f56])).
% 0.22/0.50  fof(f120,plain,(
% 0.22/0.50    v2_struct_0(sK0) | r2_hidden(sK1,sK6(sK0,sK1,sK2)) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f119,f68])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,sK6(sK0,sK1,sK2)) | (~spl7_2 | ~spl7_3 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f118,f64])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,sK6(sK0,sK1,sK2)) | (~spl7_2 | ~spl7_6)),
% 0.22/0.50    inference(subsumption_resolution,[],[f107,f60])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,sK6(sK0,sK1,sK2)) | ~spl7_6),
% 0.22/0.50    inference(resolution,[],[f80,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,sK6(X0,X1,X2))) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f139,plain,(
% 0.22/0.50    spl7_9 | spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f104,f75,f67,f63,f59,f55,f137])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    v3_pre_topc(sK3,sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(forward_demodulation,[],[f103,f94])).
% 0.22/0.50  fof(f103,plain,(
% 0.22/0.50    v3_pre_topc(sK6(sK0,sK1,sK3),sK0) | (spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f102,f56])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    v2_struct_0(sK0) | v3_pre_topc(sK6(sK0,sK1,sK3),sK0) | (~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f101,f68])).
% 0.22/0.50  fof(f101,plain,(
% 0.22/0.50    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v3_pre_topc(sK6(sK0,sK1,sK3),sK0) | (~spl7_2 | ~spl7_3 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f100,f64])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v3_pre_topc(sK6(sK0,sK1,sK3),sK0) | (~spl7_2 | ~spl7_5)),
% 0.22/0.50    inference(subsumption_resolution,[],[f85,f60])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v3_pre_topc(sK6(sK0,sK1,sK3),sK0) | ~spl7_5),
% 0.22/0.50    inference(resolution,[],[f76,f45])).
% 0.22/0.50  fof(f135,plain,(
% 0.22/0.50    ~spl7_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f27,f133])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.50    inference(flattening,[],[f11])).
% 0.22/0.50  fof(f11,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 0.22/0.50    inference(negated_conjecture,[],[f9])).
% 0.22/0.50  fof(f9,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).
% 0.22/0.50  fof(f81,plain,(
% 0.22/0.50    spl7_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f28,f79])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    spl7_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f26,f75])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f69,plain,(
% 0.22/0.50    spl7_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f29,f67])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl7_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f63])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f61,plain,(
% 0.22/0.50    spl7_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f31,f59])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ~spl7_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f30,f55])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ~v2_struct_0(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f12])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (1694)------------------------------
% 0.22/0.50  % (1694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (1694)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (1694)Memory used [KB]: 6524
% 0.22/0.50  % (1694)Time elapsed: 0.080 s
% 0.22/0.50  % (1694)------------------------------
% 0.22/0.50  % (1694)------------------------------
% 0.22/0.50  % (1693)Success in time 0.137 s
%------------------------------------------------------------------------------
