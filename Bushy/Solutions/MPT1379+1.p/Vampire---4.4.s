%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : connsp_2__t4_connsp_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:35:54 EDT 2019

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 422 expanded)
%              Number of leaves         :   30 ( 174 expanded)
%              Depth                    :   13
%              Number of atoms          :  681 (1494 expanded)
%              Number of equality atoms :   31 (  66 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10581,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f107,f111,f115,f119,f128,f132,f177,f182,f196,f213,f227,f1676,f1993,f2051,f2055,f2060,f3505,f3794,f4268,f4389,f4425,f10567,f10574,f10575,f10580])).

fof(f10580,plain,
    ( spl9_82
    | ~ spl9_162 ),
    inference(avatar_split_clause,[],[f4219,f3792,f2053])).

fof(f2053,plain,
    ( spl9_82
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_82])])).

fof(f3792,plain,
    ( spl9_162
  <=> sP8(sK1,k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_162])])).

fof(f4219,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl9_162 ),
    inference(resolution,[],[f3793,f88])).

fof(f88,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t4_connsp_2.p',d4_xboole_0)).

fof(f3793,plain,
    ( sP8(sK1,k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl9_162 ),
    inference(avatar_component_clause,[],[f3792])).

fof(f10575,plain,
    ( spl9_20
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f4338,f2058,f126,f117,f113,f109,f105,f194])).

fof(f194,plain,
    ( spl9_20
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f105,plain,
    ( spl9_1
  <=> ~ v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f109,plain,
    ( spl9_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f113,plain,
    ( spl9_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f117,plain,
    ( spl9_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f126,plain,
    ( spl9_8
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f2058,plain,
    ( spl9_84
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_84])])).

fof(f4338,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f4337,f106])).

fof(f106,plain,
    ( ~ v2_struct_0(sK0)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f105])).

fof(f4337,plain,
    ( v2_struct_0(sK0)
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f4336,f127])).

fof(f127,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f126])).

fof(f4336,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f4335,f118])).

fof(f118,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f4335,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f4334,f114])).

fof(f114,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f113])).

fof(f4334,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_84 ),
    inference(subsumption_resolution,[],[f3574,f110])).

fof(f110,plain,
    ( v2_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f109])).

fof(f3574,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ spl9_84 ),
    inference(resolution,[],[f2059,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f49,plain,(
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
    file('/export/starexec/sandbox2/benchmark/connsp_2__t4_connsp_2.p',d1_connsp_2)).

fof(f2059,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ spl9_84 ),
    inference(avatar_component_clause,[],[f2058])).

fof(f10574,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | spl9_15
    | ~ spl9_82 ),
    inference(avatar_contradiction_clause,[],[f10573])).

fof(f10573,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_15
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f209,f10572])).

fof(f10572,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f10571,f106])).

fof(f10571,plain,
    ( v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f10570,f131])).

fof(f131,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl9_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f10570,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f10569,f118])).

fof(f10569,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f10568,f114])).

fof(f10568,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl9_2
    | ~ spl9_82 ),
    inference(subsumption_resolution,[],[f3566,f110])).

fof(f3566,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl9_82 ),
    inference(resolution,[],[f2054,f80])).

fof(f2054,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl9_82 ),
    inference(avatar_component_clause,[],[f2053])).

fof(f209,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl9_15
  <=> ~ m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f10567,plain,
    ( spl9_162
    | ~ spl9_74
    | ~ spl9_130 ),
    inference(avatar_split_clause,[],[f10565,f3503,f1991,f3792])).

fof(f1991,plain,
    ( spl9_74
  <=> r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_74])])).

fof(f3503,plain,
    ( spl9_130
  <=> k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_130])])).

fof(f10565,plain,
    ( sP8(sK1,k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl9_74
    | ~ spl9_130 ),
    inference(resolution,[],[f3789,f1992])).

fof(f1992,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl9_74 ),
    inference(avatar_component_clause,[],[f1991])).

fof(f3789,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
        | sP8(X1,k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) )
    | ~ spl9_130 ),
    inference(superposition,[],[f102,f3504])).

fof(f3504,plain,
    ( k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(sK2,sK3))
    | ~ spl9_130 ),
    inference(avatar_component_clause,[],[f3503])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | sP8(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( sP8(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4425,plain,
    ( spl9_18
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_74 ),
    inference(avatar_split_clause,[],[f4331,f1991,f130,f117,f113,f109,f105,f180])).

fof(f180,plain,
    ( spl9_18
  <=> m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_18])])).

fof(f4331,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_74 ),
    inference(subsumption_resolution,[],[f4330,f106])).

fof(f4330,plain,
    ( v2_struct_0(sK0)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_74 ),
    inference(subsumption_resolution,[],[f4329,f434])).

fof(f434,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(sK2,X0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_10 ),
    inference(superposition,[],[f422,f94])).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t4_connsp_2.p',commutativity_k3_xboole_0)).

fof(f422,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_10 ),
    inference(superposition,[],[f155,f156])).

fof(f156,plain,
    ( ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,sK2) = k3_xboole_0(X4,sK2)
    | ~ spl9_10 ),
    inference(resolution,[],[f131,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t4_connsp_2.p',redefinition_k9_subset_1)).

fof(f155,plain,
    ( ! [X3] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X3,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_10 ),
    inference(resolution,[],[f131,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t4_connsp_2.p',dt_k9_subset_1)).

fof(f4329,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_74 ),
    inference(subsumption_resolution,[],[f4328,f118])).

fof(f4328,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_74 ),
    inference(subsumption_resolution,[],[f4327,f114])).

fof(f4327,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_2
    | ~ spl9_74 ),
    inference(subsumption_resolution,[],[f4320,f110])).

fof(f4320,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_74 ),
    inference(resolution,[],[f1992,f80])).

fof(f4389,plain,
    ( spl9_84
    | ~ spl9_162 ),
    inference(avatar_split_clause,[],[f4220,f3792,f2058])).

fof(f4220,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ spl9_162 ),
    inference(resolution,[],[f3793,f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f4268,plain,
    ( spl9_74
    | ~ spl9_130
    | ~ spl9_162 ),
    inference(avatar_split_clause,[],[f4222,f3792,f3503,f1991])).

fof(f4222,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl9_130
    | ~ spl9_162 ),
    inference(forward_demodulation,[],[f4221,f3504])).

fof(f4221,plain,
    ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | ~ spl9_162 ),
    inference(resolution,[],[f3793,f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP8(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3794,plain,
    ( spl9_162
    | ~ spl9_82
    | ~ spl9_84 ),
    inference(avatar_split_clause,[],[f3738,f2058,f2053,f3792])).

fof(f3738,plain,
    ( sP8(sK1,k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl9_82
    | ~ spl9_84 ),
    inference(resolution,[],[f3571,f2059])).

fof(f3571,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | sP8(sK1,X1,k1_tops_1(sK0,sK2)) )
    | ~ spl9_82 ),
    inference(resolution,[],[f2054,f87])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | sP8(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f3505,plain,
    ( spl9_130
    | ~ spl9_26
    | ~ spl9_68 ),
    inference(avatar_split_clause,[],[f1853,f1674,f225,f3503])).

fof(f225,plain,
    ( spl9_26
  <=> m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f1674,plain,
    ( spl9_68
  <=> k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_68])])).

fof(f1853,plain,
    ( k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(sK2,sK3))
    | ~ spl9_26
    | ~ spl9_68 ),
    inference(superposition,[],[f1675,f260])).

fof(f260,plain,
    ( ! [X5] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),X5) = k3_xboole_0(X5,k1_tops_1(sK0,sK3))
    | ~ spl9_26 ),
    inference(forward_demodulation,[],[f247,f246])).

fof(f246,plain,
    ( ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,k1_tops_1(sK0,sK3)) = k3_xboole_0(X4,k1_tops_1(sK0,sK3))
    | ~ spl9_26 ),
    inference(resolution,[],[f226,f74])).

fof(f226,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f225])).

fof(f247,plain,
    ( ! [X5] : k9_subset_1(u1_struct_0(sK0),X5,k1_tops_1(sK0,sK3)) = k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),X5)
    | ~ spl9_26 ),
    inference(resolution,[],[f226,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t4_connsp_2.p',commutativity_k9_subset_1)).

fof(f1675,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k3_xboole_0(sK2,sK3))
    | ~ spl9_68 ),
    inference(avatar_component_clause,[],[f1674])).

fof(f2060,plain,
    ( spl9_84
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_20 ),
    inference(avatar_split_clause,[],[f2047,f194,f126,f117,f113,f109,f105,f2058])).

fof(f2047,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_20 ),
    inference(subsumption_resolution,[],[f2045,f118])).

fof(f2045,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_20 ),
    inference(resolution,[],[f195,f146])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK3,sK0,X0)
        | r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f145,f106])).

fof(f145,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ m1_connsp_2(sK3,sK0,X0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f144,f114])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ m1_connsp_2(sK3,sK0,X0) )
    | ~ spl9_2
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f135,f110])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ m1_connsp_2(sK3,sK0,X0) )
    | ~ spl9_8 ),
    inference(resolution,[],[f127,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f195,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl9_20 ),
    inference(avatar_component_clause,[],[f194])).

fof(f2055,plain,
    ( spl9_82
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f2044,f172,f130,f117,f113,f109,f105,f2053])).

fof(f172,plain,
    ( spl9_14
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f2044,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(subsumption_resolution,[],[f2042,f118])).

fof(f2042,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10
    | ~ spl9_14 ),
    inference(resolution,[],[f173,f163])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK2,sK0,X0)
        | r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f162,f106])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ m1_connsp_2(sK2,sK0,X0) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f161,f114])).

fof(f161,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ m1_connsp_2(sK2,sK0,X0) )
    | ~ spl9_2
    | ~ spl9_10 ),
    inference(subsumption_resolution,[],[f152,f110])).

fof(f152,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ m1_connsp_2(sK2,sK0,X0) )
    | ~ spl9_10 ),
    inference(resolution,[],[f131,f81])).

fof(f173,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f172])).

fof(f2051,plain,
    ( ~ spl9_19
    | ~ spl9_8
    | spl9_17 ),
    inference(avatar_split_clause,[],[f2041,f211,f126,f2049])).

fof(f2049,plain,
    ( spl9_19
  <=> ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f211,plain,
    ( spl9_17
  <=> ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f2041,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_8
    | ~ spl9_17 ),
    inference(forward_demodulation,[],[f212,f139])).

fof(f139,plain,
    ( ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,sK3) = k3_xboole_0(X4,sK3)
    | ~ spl9_8 ),
    inference(resolution,[],[f127,f74])).

fof(f212,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f211])).

fof(f1993,plain,
    ( spl9_74
    | spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18 ),
    inference(avatar_split_clause,[],[f1988,f180,f126,f117,f113,f109,f105,f1991])).

fof(f1988,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_6
    | ~ spl9_8
    | ~ spl9_18 ),
    inference(subsumption_resolution,[],[f1984,f118])).

fof(f1984,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_18 ),
    inference(resolution,[],[f317,f181])).

fof(f181,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_18 ),
    inference(avatar_component_clause,[],[f180])).

fof(f317,plain,
    ( ! [X2,X3] :
        ( ~ m1_connsp_2(k3_xboole_0(X3,sK3),sK0,X2)
        | r2_hidden(X2,k1_tops_1(sK0,k3_xboole_0(X3,sK3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(forward_demodulation,[],[f316,f139])).

fof(f316,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,k1_tops_1(sK0,k3_xboole_0(X3,sK3)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X3,sK3),sK0,X2) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(forward_demodulation,[],[f315,f139])).

fof(f315,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(X2,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK3)))
        | ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X3,sK3),sK0,X2) )
    | ~ spl9_1
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f314,f106])).

fof(f314,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X2,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK3)))
        | ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X3,sK3),sK0,X2) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f313,f114])).

fof(f313,plain,
    ( ! [X2,X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X2,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK3)))
        | ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X3,sK3),sK0,X2) )
    | ~ spl9_2
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f301,f110])).

fof(f301,plain,
    ( ! [X2,X3] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X2,k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X3,sK3)))
        | ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X3,sK3),sK0,X2) )
    | ~ spl9_8 ),
    inference(resolution,[],[f138,f81])).

fof(f138,plain,
    ( ! [X3] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X3,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_8 ),
    inference(resolution,[],[f127,f75])).

fof(f1676,plain,
    ( spl9_68
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(avatar_split_clause,[],[f567,f130,f126,f113,f109,f1674])).

fof(f567,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k3_xboole_0(sK2,sK3))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(forward_demodulation,[],[f566,f94])).

fof(f566,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k3_xboole_0(sK3,sK2))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(forward_demodulation,[],[f545,f156])).

fof(f545,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK3,sK2))
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8
    | ~ spl9_10 ),
    inference(resolution,[],[f148,f131])).

fof(f148,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK3,X1)) )
    | ~ spl9_2
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f147,f110])).

fof(f147,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK3,X1)) )
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f136,f114])).

fof(f136,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK3,X1)) )
    | ~ spl9_8 ),
    inference(resolution,[],[f127,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t4_connsp_2.p',t46_tops_1)).

fof(f227,plain,
    ( spl9_26
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f142,f126,f113,f225])).

fof(f142,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4
    | ~ spl9_8 ),
    inference(subsumption_resolution,[],[f133,f114])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_8 ),
    inference(resolution,[],[f127,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    file('/export/starexec/sandbox2/benchmark/connsp_2__t4_connsp_2.p',dt_k1_tops_1)).

fof(f213,plain,
    ( ~ spl9_21
    | ~ spl9_15
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f64,f211,f208,f205])).

fof(f205,plain,
    ( spl9_21
  <=> ~ m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_21])])).

fof(f64,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
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
                    <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
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
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/connsp_2__t4_connsp_2.p',t4_connsp_2)).

fof(f196,plain,
    ( spl9_20
    | spl9_16 ),
    inference(avatar_split_clause,[],[f66,f175,f194])).

fof(f175,plain,
    ( spl9_16
  <=> m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f66,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f182,plain,
    ( spl9_18
    | ~ spl9_8
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f178,f175,f126,f180])).

fof(f178,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl9_8
    | ~ spl9_16 ),
    inference(forward_demodulation,[],[f176,f139])).

fof(f176,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f175])).

fof(f177,plain,
    ( spl9_14
    | spl9_16 ),
    inference(avatar_split_clause,[],[f65,f175,f172])).

fof(f65,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f132,plain,(
    spl9_10 ),
    inference(avatar_split_clause,[],[f68,f130])).

fof(f68,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f128,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f67,f126])).

fof(f67,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f119,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f69,f117])).

fof(f69,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f115,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f72,f113])).

fof(f72,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f111,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f71,f109])).

fof(f71,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f70,f105])).

fof(f70,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
