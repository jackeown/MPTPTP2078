%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 221 expanded)
%              Number of leaves         :   30 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  359 ( 707 expanded)
%              Number of equality atoms :   44 (  95 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f974,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f98,f117,f123,f129,f142,f169,f229,f230,f326,f494,f503,f552,f973])).

fof(f973,plain,
    ( ~ spl8_2
    | ~ spl8_3
    | spl8_5
    | ~ spl8_6
    | ~ spl8_78
    | ~ spl8_87 ),
    inference(avatar_split_clause,[],[f972,f550,f500,f95,f90,f80,f75])).

fof(f75,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f80,plain,
    ( spl8_3
  <=> v4_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f90,plain,
    ( spl8_5
  <=> v4_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f95,plain,
    ( spl8_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f500,plain,
    ( spl8_78
  <=> sK3 = k1_setfam_1(k2_tarski(sK3,u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).

fof(f550,plain,
    ( spl8_87
  <=> ! [X0] :
        ( v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),sK2)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).

fof(f972,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | v4_pre_topc(sK3,sK2)
    | ~ v4_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl8_78
    | ~ spl8_87 ),
    inference(superposition,[],[f897,f502])).

fof(f502,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,u1_struct_0(sK2)))
    | ~ spl8_78 ),
    inference(avatar_component_clause,[],[f500])).

fof(f897,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2)))
        | v4_pre_topc(k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))),sK2)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl8_87 ),
    inference(forward_demodulation,[],[f896,f191])).

fof(f191,plain,(
    ! [X2,X3] : k9_subset_1(X2,X3,X2) = k1_setfam_1(k2_tarski(X3,X2)) ),
    inference(resolution,[],[f64,f105])).

fof(f105,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f36,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f60,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f896,plain,
    ( ! [X0] :
        ( v4_pre_topc(k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))),sK2)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_87 ),
    inference(forward_demodulation,[],[f551,f191])).

fof(f551,plain,
    ( ! [X0] :
        ( v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),sK2)
        | ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) )
    | ~ spl8_87 ),
    inference(avatar_component_clause,[],[f550])).

fof(f552,plain,
    ( ~ spl8_1
    | spl8_87
    | ~ spl8_4
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f548,f126,f85,f550,f70])).

fof(f70,plain,
    ( spl8_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f85,plain,
    ( spl8_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f126,plain,
    ( spl8_11
  <=> u1_struct_0(sK2) = k2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f548,plain,
    ( ! [X0] :
        ( v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),sK2)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0) )
    | ~ spl8_4
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f547,f128])).

fof(f128,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f547,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl8_4
    | ~ spl8_11 ),
    inference(forward_demodulation,[],[f544,f128])).

fof(f544,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v4_pre_topc(X0,sK0)
        | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2) )
    | ~ spl8_4 ),
    inference(resolution,[],[f66,f87])).

fof(f87,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | v4_pre_topc(X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v4_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v4_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).

fof(f503,plain,
    ( spl8_78
    | ~ spl8_77 ),
    inference(avatar_split_clause,[],[f498,f491,f500])).

% (22836)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f491,plain,
    ( spl8_77
  <=> r1_tarski(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f498,plain,
    ( sK3 = k1_setfam_1(k2_tarski(sK3,u1_struct_0(sK2)))
    | ~ spl8_77 ),
    inference(resolution,[],[f493,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f57,f56])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f493,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2))
    | ~ spl8_77 ),
    inference(avatar_component_clause,[],[f491])).

fof(f494,plain,
    ( spl8_77
    | ~ spl8_27
    | ~ spl8_45 ),
    inference(avatar_split_clause,[],[f489,f323,f226,f491])).

fof(f226,plain,
    ( spl8_27
  <=> r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f323,plain,
    ( spl8_45
  <=> sK3 = k2_struct_0(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f489,plain,
    ( r1_tarski(sK3,u1_struct_0(sK2))
    | ~ spl8_27
    | ~ spl8_45 ),
    inference(forward_demodulation,[],[f228,f325])).

fof(f325,plain,
    ( sK3 = k2_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl8_45 ),
    inference(avatar_component_clause,[],[f323])).

fof(f228,plain,
    ( r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),u1_struct_0(sK2))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f226])).

fof(f326,plain,
    ( spl8_45
    | ~ spl8_9
    | ~ spl8_13
    | ~ spl8_6
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f316,f166,f95,f139,f114,f323])).

fof(f114,plain,
    ( spl8_9
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

% (22826)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f139,plain,
    ( spl8_13
  <=> v1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f166,plain,
    ( spl8_17
  <=> m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f316,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ v1_pre_topc(k1_pre_topc(sK2,sK3))
    | ~ l1_pre_topc(sK2)
    | sK3 = k2_struct_0(k1_pre_topc(sK2,sK3))
    | ~ spl8_17 ),
    inference(resolution,[],[f67,f168])).

fof(f168,plain,
    ( m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f166])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f230,plain,
    ( spl8_26
    | ~ spl8_9
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f219,f166,f114,f222])).

fof(f222,plain,
    ( spl8_26
  <=> l1_pre_topc(k1_pre_topc(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).

fof(f219,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(k1_pre_topc(sK2,sK3))
    | ~ spl8_17 ),
    inference(resolution,[],[f168,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f229,plain,
    ( ~ spl8_9
    | ~ spl8_26
    | spl8_27
    | ~ spl8_11
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f220,f166,f126,f226,f222,f114])).

fof(f220,plain,
    ( r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),u1_struct_0(sK2))
    | ~ l1_pre_topc(k1_pre_topc(sK2,sK3))
    | ~ l1_pre_topc(sK2)
    | ~ spl8_11
    | ~ spl8_17 ),
    inference(forward_demodulation,[],[f218,f128])).

fof(f218,plain,
    ( ~ l1_pre_topc(k1_pre_topc(sK2,sK3))
    | r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),k2_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ spl8_17 ),
    inference(resolution,[],[f168,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f169,plain,
    ( spl8_17
    | ~ spl8_9
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f158,f95,f114,f166])).

fof(f158,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)
    | ~ spl8_6 ),
    inference(resolution,[],[f59,f97])).

fof(f97,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f142,plain,
    ( spl8_13
    | ~ spl8_9
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f131,f95,f114,f139])).

fof(f131,plain,
    ( ~ l1_pre_topc(sK2)
    | v1_pre_topc(k1_pre_topc(sK2,sK3))
    | ~ spl8_6 ),
    inference(resolution,[],[f58,f97])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f129,plain,
    ( spl8_11
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f124,f120,f126])).

fof(f120,plain,
    ( spl8_10
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f124,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2)
    | ~ spl8_10 ),
    inference(resolution,[],[f122,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f122,plain,
    ( l1_struct_0(sK2)
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f120])).

fof(f123,plain,
    ( spl8_10
    | ~ spl8_9 ),
    inference(avatar_split_clause,[],[f118,f114,f120])).

fof(f118,plain,
    ( l1_struct_0(sK2)
    | ~ spl8_9 ),
    inference(resolution,[],[f116,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f116,plain,
    ( l1_pre_topc(sK2)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( spl8_9
    | ~ spl8_1
    | ~ spl8_4 ),
    inference(avatar_split_clause,[],[f112,f85,f70,f114])).

fof(f112,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2)
    | ~ spl8_4 ),
    inference(resolution,[],[f49,f87])).

fof(f98,plain,(
    spl8_6 ),
    inference(avatar_split_clause,[],[f28,f95])).

fof(f28,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v4_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v4_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v4_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v4_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v4_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).

fof(f93,plain,(
    ~ spl8_5 ),
    inference(avatar_split_clause,[],[f30,f90])).

fof(f30,plain,(
    ~ v4_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f88,plain,(
    spl8_4 ),
    inference(avatar_split_clause,[],[f31,f85])).

fof(f31,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f83,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f62,f80])).

fof(f62,plain,(
    v4_pre_topc(sK3,sK0) ),
    inference(definition_unfolding,[],[f32,f29])).

fof(f29,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f61,f75])).

fof(f61,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(definition_unfolding,[],[f33,f29])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f73,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f34,f70])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:30:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (22817)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (22840)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (22831)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (22823)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (22825)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (22841)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (22833)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (22832)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (22819)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (22822)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (22818)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (22840)Refutation not found, incomplete strategy% (22840)------------------------------
% 0.21/0.54  % (22840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22840)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22840)Memory used [KB]: 10746
% 0.21/0.54  % (22840)Time elapsed: 0.122 s
% 0.21/0.54  % (22840)------------------------------
% 0.21/0.54  % (22840)------------------------------
% 0.21/0.54  % (22819)Refutation not found, incomplete strategy% (22819)------------------------------
% 0.21/0.54  % (22819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22819)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22819)Memory used [KB]: 10746
% 0.21/0.54  % (22819)Time elapsed: 0.125 s
% 0.21/0.54  % (22819)------------------------------
% 0.21/0.54  % (22819)------------------------------
% 0.21/0.54  % (22824)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (22846)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (22820)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (22821)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (22828)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (22833)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (22838)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (22847)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (22835)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (22842)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (22835)Refutation not found, incomplete strategy% (22835)------------------------------
% 0.21/0.55  % (22835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22835)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22835)Memory used [KB]: 10618
% 0.21/0.55  % (22835)Time elapsed: 0.135 s
% 0.21/0.55  % (22835)------------------------------
% 0.21/0.55  % (22835)------------------------------
% 0.21/0.55  % (22825)Refutation not found, incomplete strategy% (22825)------------------------------
% 0.21/0.55  % (22825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22825)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22825)Memory used [KB]: 10874
% 0.21/0.55  % (22825)Time elapsed: 0.130 s
% 0.21/0.55  % (22825)------------------------------
% 0.21/0.55  % (22825)------------------------------
% 0.21/0.55  % (22827)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (22839)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (22827)Refutation not found, incomplete strategy% (22827)------------------------------
% 0.21/0.56  % (22827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22827)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22827)Memory used [KB]: 10746
% 0.21/0.56  % (22827)Time elapsed: 0.148 s
% 0.21/0.56  % (22827)------------------------------
% 0.21/0.56  % (22827)------------------------------
% 0.21/0.56  % (22845)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f974,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f73,f78,f83,f88,f93,f98,f117,f123,f129,f142,f169,f229,f230,f326,f494,f503,f552,f973])).
% 0.21/0.56  fof(f973,plain,(
% 0.21/0.56    ~spl8_2 | ~spl8_3 | spl8_5 | ~spl8_6 | ~spl8_78 | ~spl8_87),
% 0.21/0.56    inference(avatar_split_clause,[],[f972,f550,f500,f95,f90,f80,f75])).
% 0.21/0.56  fof(f75,plain,(
% 0.21/0.56    spl8_2 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.56  fof(f80,plain,(
% 0.21/0.56    spl8_3 <=> v4_pre_topc(sK3,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    spl8_5 <=> v4_pre_topc(sK3,sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    spl8_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.56  fof(f500,plain,(
% 0.21/0.56    spl8_78 <=> sK3 = k1_setfam_1(k2_tarski(sK3,u1_struct_0(sK2)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_78])])).
% 0.21/0.56  fof(f550,plain,(
% 0.21/0.56    spl8_87 <=> ! [X0] : (v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),sK2) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_87])])).
% 0.21/0.56  fof(f972,plain,(
% 0.21/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(sK3,sK2) | ~v4_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl8_78 | ~spl8_87)),
% 0.21/0.56    inference(superposition,[],[f897,f502])).
% 0.21/0.56  fof(f502,plain,(
% 0.21/0.56    sK3 = k1_setfam_1(k2_tarski(sK3,u1_struct_0(sK2))) | ~spl8_78),
% 0.21/0.56    inference(avatar_component_clause,[],[f500])).
% 0.21/0.56  fof(f897,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))),k1_zfmisc_1(u1_struct_0(sK2))) | v4_pre_topc(k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))),sK2) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl8_87),
% 0.21/0.56    inference(forward_demodulation,[],[f896,f191])).
% 0.21/0.56  fof(f191,plain,(
% 0.21/0.56    ( ! [X2,X3] : (k9_subset_1(X2,X3,X2) = k1_setfam_1(k2_tarski(X3,X2))) )),
% 0.21/0.56    inference(resolution,[],[f64,f105])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(forward_demodulation,[],[f36,f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 0.21/0.56    inference(definition_unfolding,[],[f60,f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.56  fof(f896,plain,(
% 0.21/0.56    ( ! [X0] : (v4_pre_topc(k1_setfam_1(k2_tarski(X0,u1_struct_0(sK2))),sK2) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl8_87),
% 0.21/0.56    inference(forward_demodulation,[],[f551,f191])).
% 0.21/0.56  fof(f551,plain,(
% 0.21/0.56    ( ! [X0] : (v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),sK2) | ~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2)))) ) | ~spl8_87),
% 0.21/0.56    inference(avatar_component_clause,[],[f550])).
% 0.21/0.56  fof(f552,plain,(
% 0.21/0.56    ~spl8_1 | spl8_87 | ~spl8_4 | ~spl8_11),
% 0.21/0.56    inference(avatar_split_clause,[],[f548,f126,f85,f550,f70])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    spl8_1 <=> l1_pre_topc(sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    spl8_4 <=> m1_pre_topc(sK2,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.56  fof(f126,plain,(
% 0.21/0.56    spl8_11 <=> u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.56  fof(f548,plain,(
% 0.21/0.56    ( ! [X0] : (v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),sK2) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0)) ) | (~spl8_4 | ~spl8_11)),
% 0.21/0.56    inference(forward_demodulation,[],[f547,f128])).
% 0.21/0.56  fof(f128,plain,(
% 0.21/0.56    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl8_11),
% 0.21/0.56    inference(avatar_component_clause,[],[f126])).
% 0.21/0.56  fof(f547,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,u1_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | (~spl8_4 | ~spl8_11)),
% 0.21/0.56    inference(forward_demodulation,[],[f544,f128])).
% 0.21/0.56  fof(f544,plain,(
% 0.21/0.56    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | v4_pre_topc(k9_subset_1(u1_struct_0(sK2),X0,k2_struct_0(sK2)),sK2)) ) | ~spl8_4),
% 0.21/0.56    inference(resolution,[],[f66,f87])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    m1_pre_topc(sK2,sK0) | ~spl8_4),
% 0.21/0.56    inference(avatar_component_clause,[],[f85])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | v4_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)) )),
% 0.21/0.56    inference(equality_resolution,[],[f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | v4_pre_topc(X2,X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v4_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v4_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_pre_topc)).
% 0.21/0.56  fof(f503,plain,(
% 0.21/0.56    spl8_78 | ~spl8_77),
% 0.21/0.56    inference(avatar_split_clause,[],[f498,f491,f500])).
% 0.21/0.56  % (22836)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  fof(f491,plain,(
% 0.21/0.56    spl8_77 <=> r1_tarski(sK3,u1_struct_0(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).
% 0.21/0.56  fof(f498,plain,(
% 0.21/0.56    sK3 = k1_setfam_1(k2_tarski(sK3,u1_struct_0(sK2))) | ~spl8_77),
% 0.21/0.56    inference(resolution,[],[f493,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 0.21/0.56    inference(definition_unfolding,[],[f57,f56])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.56  fof(f493,plain,(
% 0.21/0.56    r1_tarski(sK3,u1_struct_0(sK2)) | ~spl8_77),
% 0.21/0.56    inference(avatar_component_clause,[],[f491])).
% 0.21/0.56  fof(f494,plain,(
% 0.21/0.56    spl8_77 | ~spl8_27 | ~spl8_45),
% 0.21/0.56    inference(avatar_split_clause,[],[f489,f323,f226,f491])).
% 0.21/0.56  fof(f226,plain,(
% 0.21/0.56    spl8_27 <=> r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),u1_struct_0(sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.56  fof(f323,plain,(
% 0.21/0.56    spl8_45 <=> sK3 = k2_struct_0(k1_pre_topc(sK2,sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 0.21/0.56  fof(f489,plain,(
% 0.21/0.56    r1_tarski(sK3,u1_struct_0(sK2)) | (~spl8_27 | ~spl8_45)),
% 0.21/0.56    inference(forward_demodulation,[],[f228,f325])).
% 0.21/0.56  fof(f325,plain,(
% 0.21/0.56    sK3 = k2_struct_0(k1_pre_topc(sK2,sK3)) | ~spl8_45),
% 0.21/0.56    inference(avatar_component_clause,[],[f323])).
% 0.21/0.56  fof(f228,plain,(
% 0.21/0.56    r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),u1_struct_0(sK2)) | ~spl8_27),
% 0.21/0.56    inference(avatar_component_clause,[],[f226])).
% 0.21/0.56  fof(f326,plain,(
% 0.21/0.56    spl8_45 | ~spl8_9 | ~spl8_13 | ~spl8_6 | ~spl8_17),
% 0.21/0.56    inference(avatar_split_clause,[],[f316,f166,f95,f139,f114,f323])).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    spl8_9 <=> l1_pre_topc(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.56  % (22826)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  fof(f139,plain,(
% 0.21/0.56    spl8_13 <=> v1_pre_topc(k1_pre_topc(sK2,sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.56  fof(f166,plain,(
% 0.21/0.56    spl8_17 <=> m1_pre_topc(k1_pre_topc(sK2,sK3),sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.56  fof(f316,plain,(
% 0.21/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~v1_pre_topc(k1_pre_topc(sK2,sK3)) | ~l1_pre_topc(sK2) | sK3 = k2_struct_0(k1_pre_topc(sK2,sK3)) | ~spl8_17),
% 0.21/0.56    inference(resolution,[],[f67,f168])).
% 0.21/0.56  fof(f168,plain,(
% 0.21/0.56    m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) | ~spl8_17),
% 0.21/0.56    inference(avatar_component_clause,[],[f166])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(k1_pre_topc(X0,X1)) | ~l1_pre_topc(X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.21/0.56    inference(equality_resolution,[],[f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.21/0.56  fof(f230,plain,(
% 0.21/0.56    spl8_26 | ~spl8_9 | ~spl8_17),
% 0.21/0.56    inference(avatar_split_clause,[],[f219,f166,f114,f222])).
% 0.21/0.56  fof(f222,plain,(
% 0.21/0.56    spl8_26 <=> l1_pre_topc(k1_pre_topc(sK2,sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_26])])).
% 0.21/0.56  fof(f219,plain,(
% 0.21/0.56    ~l1_pre_topc(sK2) | l1_pre_topc(k1_pre_topc(sK2,sK3)) | ~spl8_17),
% 0.21/0.56    inference(resolution,[],[f168,f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.56  fof(f229,plain,(
% 0.21/0.56    ~spl8_9 | ~spl8_26 | spl8_27 | ~spl8_11 | ~spl8_17),
% 0.21/0.56    inference(avatar_split_clause,[],[f220,f166,f126,f226,f222,f114])).
% 0.21/0.56  fof(f220,plain,(
% 0.21/0.56    r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),u1_struct_0(sK2)) | ~l1_pre_topc(k1_pre_topc(sK2,sK3)) | ~l1_pre_topc(sK2) | (~spl8_11 | ~spl8_17)),
% 0.21/0.56    inference(forward_demodulation,[],[f218,f128])).
% 0.21/0.56  fof(f218,plain,(
% 0.21/0.56    ~l1_pre_topc(k1_pre_topc(sK2,sK3)) | r1_tarski(k2_struct_0(k1_pre_topc(sK2,sK3)),k2_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~spl8_17),
% 0.21/0.56    inference(resolution,[],[f168,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.21/0.56  fof(f169,plain,(
% 0.21/0.56    spl8_17 | ~spl8_9 | ~spl8_6),
% 0.21/0.56    inference(avatar_split_clause,[],[f158,f95,f114,f166])).
% 0.21/0.56  fof(f158,plain,(
% 0.21/0.56    ~l1_pre_topc(sK2) | m1_pre_topc(k1_pre_topc(sK2,sK3),sK2) | ~spl8_6),
% 0.21/0.56    inference(resolution,[],[f59,f97])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) | ~spl8_6),
% 0.21/0.56    inference(avatar_component_clause,[],[f95])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    spl8_13 | ~spl8_9 | ~spl8_6),
% 0.21/0.56    inference(avatar_split_clause,[],[f131,f95,f114,f139])).
% 0.21/0.56  fof(f131,plain,(
% 0.21/0.56    ~l1_pre_topc(sK2) | v1_pre_topc(k1_pre_topc(sK2,sK3)) | ~spl8_6),
% 0.21/0.56    inference(resolution,[],[f58,f97])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_pre_topc(k1_pre_topc(X0,X1))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f129,plain,(
% 0.21/0.56    spl8_11 | ~spl8_10),
% 0.21/0.56    inference(avatar_split_clause,[],[f124,f120,f126])).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    spl8_10 <=> l1_struct_0(sK2)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.56  fof(f124,plain,(
% 0.21/0.56    u1_struct_0(sK2) = k2_struct_0(sK2) | ~spl8_10),
% 0.21/0.56    inference(resolution,[],[f122,f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    l1_struct_0(sK2) | ~spl8_10),
% 0.21/0.56    inference(avatar_component_clause,[],[f120])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    spl8_10 | ~spl8_9),
% 0.21/0.56    inference(avatar_split_clause,[],[f118,f114,f120])).
% 0.21/0.56  fof(f118,plain,(
% 0.21/0.56    l1_struct_0(sK2) | ~spl8_9),
% 0.21/0.56    inference(resolution,[],[f116,f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    l1_pre_topc(sK2) | ~spl8_9),
% 0.21/0.56    inference(avatar_component_clause,[],[f114])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    spl8_9 | ~spl8_1 | ~spl8_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f112,f85,f70,f114])).
% 0.21/0.56  fof(f112,plain,(
% 0.21/0.56    ~l1_pre_topc(sK0) | l1_pre_topc(sK2) | ~spl8_4),
% 0.21/0.56    inference(resolution,[],[f49,f87])).
% 0.21/0.56  fof(f98,plain,(
% 0.21/0.56    spl8_6),
% 0.21/0.56    inference(avatar_split_clause,[],[f28,f95])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v4_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.56    inference(flattening,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v4_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v4_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,negated_conjecture,(
% 0.21/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.56    inference(negated_conjecture,[],[f13])).
% 0.21/0.56  fof(f13,conjecture,(
% 0.21/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v4_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v4_pre_topc(X3,X2)))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_2)).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ~spl8_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f30,f90])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ~v4_pre_topc(sK3,sK2)),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    spl8_4),
% 0.21/0.56    inference(avatar_split_clause,[],[f31,f85])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    m1_pre_topc(sK2,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    spl8_3),
% 0.21/0.56    inference(avatar_split_clause,[],[f62,f80])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    v4_pre_topc(sK3,sK0)),
% 0.21/0.56    inference(definition_unfolding,[],[f32,f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    sK1 = sK3),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    v4_pre_topc(sK1,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f78,plain,(
% 0.21/0.56    spl8_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f61,f75])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    inference(definition_unfolding,[],[f33,f29])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    spl8_1),
% 0.21/0.56    inference(avatar_split_clause,[],[f34,f70])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    l1_pre_topc(sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f16])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (22833)------------------------------
% 0.21/0.56  % (22833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22833)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (22833)Memory used [KB]: 11385
% 0.21/0.56  % (22833)Time elapsed: 0.128 s
% 0.21/0.56  % (22833)------------------------------
% 0.21/0.56  % (22833)------------------------------
% 0.21/0.56  % (22830)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (22829)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (22814)Success in time 0.198 s
%------------------------------------------------------------------------------
