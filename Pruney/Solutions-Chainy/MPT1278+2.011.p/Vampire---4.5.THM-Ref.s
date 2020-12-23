%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:51 EST 2020

% Result     : Theorem 1.54s
% Output     : Refutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 516 expanded)
%              Number of leaves         :   47 ( 211 expanded)
%              Depth                    :   12
%              Number of atoms          :  507 (1110 expanded)
%              Number of equality atoms :   92 ( 299 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f803,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f111,f120,f133,f175,f183,f206,f212,f220,f262,f275,f301,f383,f393,f440,f485,f551,f554,f568,f576,f644,f746,f749,f795])).

fof(f795,plain,
    ( spl2_3
    | ~ spl2_62
    | ~ spl2_75 ),
    inference(avatar_split_clause,[],[f794,f641,f557,f85])).

fof(f85,plain,
    ( spl2_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f557,plain,
    ( spl2_62
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).

fof(f641,plain,
    ( spl2_75
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).

fof(f794,plain,
    ( k1_xboole_0 = sK1
    | ~ spl2_62
    | ~ spl2_75 ),
    inference(forward_demodulation,[],[f764,f163])).

fof(f163,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f114,f152])).

fof(f152,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f151,f49])).

fof(f49,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f151,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f143,f50])).

fof(f50,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f143,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f73,f49])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f66,f67,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f114,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(resolution,[],[f69,f104])).

fof(f104,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f51,f48])).

fof(f48,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f764,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl2_62
    | ~ spl2_75 ),
    inference(backward_demodulation,[],[f643,f558])).

fof(f558,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl2_62 ),
    inference(avatar_component_clause,[],[f557])).

fof(f643,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_75 ),
    inference(avatar_component_clause,[],[f641])).

fof(f749,plain,
    ( ~ spl2_1
    | spl2_62
    | ~ spl2_57
    | ~ spl2_61 ),
    inference(avatar_split_clause,[],[f748,f546,f520,f557,f75])).

fof(f75,plain,
    ( spl2_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f520,plain,
    ( spl2_57
  <=> v1_tops_1(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f546,plain,
    ( spl2_61
  <=> u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).

fof(f748,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_57
    | ~ spl2_61 ),
    inference(forward_demodulation,[],[f747,f547])).

fof(f547,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl2_61 ),
    inference(avatar_component_clause,[],[f546])).

fof(f747,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_57 ),
    inference(resolution,[],[f522,f234])).

fof(f234,plain,(
    ! [X0] :
      ( ~ v1_tops_1(u1_struct_0(X0),X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f59,f104])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = k2_struct_0(X0)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f522,plain,
    ( v1_tops_1(u1_struct_0(sK0),sK0)
    | ~ spl2_57 ),
    inference(avatar_component_clause,[],[f520])).

fof(f746,plain,
    ( spl2_57
    | ~ spl2_1
    | ~ spl2_63 ),
    inference(avatar_split_clause,[],[f745,f565,f75,f520])).

fof(f565,plain,
    ( spl2_63
  <=> v2_tops_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f745,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_1(u1_struct_0(sK0),sK0)
    | ~ spl2_63 ),
    inference(resolution,[],[f744,f567])).

fof(f567,plain,
    ( v2_tops_1(k1_xboole_0,sK0)
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f565])).

fof(f744,plain,(
    ! [X1] :
      ( ~ v2_tops_1(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1)
      | v1_tops_1(u1_struct_0(X1),X1) ) ),
    inference(forward_demodulation,[],[f239,f161])).

fof(f161,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f134,f152])).

% (6311)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f134,plain,(
    ! [X0] : k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f127,f114])).

fof(f127,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(resolution,[],[f70,f104])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f239,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | v1_tops_1(k3_subset_1(u1_struct_0(X1),k1_xboole_0),X1)
      | ~ v2_tops_1(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f61,f162])).

fof(f162,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f121,f152])).

fof(f121,plain,(
    ! [X0] : m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f106,f114])).

fof(f106,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,X0),k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f68,f104])).

% (6314)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f644,plain,
    ( spl2_75
    | ~ spl2_53
    | ~ spl2_64 ),
    inference(avatar_split_clause,[],[f587,f573,f482,f641])).

fof(f482,plain,
    ( spl2_53
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).

fof(f573,plain,
    ( spl2_64
  <=> k4_xboole_0(u1_struct_0(sK0),sK1) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).

fof(f587,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl2_53
    | ~ spl2_64 ),
    inference(backward_demodulation,[],[f484,f575])).

fof(f575,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_struct_0(sK0)
    | ~ spl2_64 ),
    inference(avatar_component_clause,[],[f573])).

fof(f484,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_53 ),
    inference(avatar_component_clause,[],[f482])).

fof(f576,plain,
    ( spl2_64
    | ~ spl2_8
    | ~ spl2_22
    | ~ spl2_45 ),
    inference(avatar_split_clause,[],[f571,f437,f298,f117,f573])).

fof(f117,plain,
    ( spl2_8
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f298,plain,
    ( spl2_22
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f437,plain,
    ( spl2_45
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).

fof(f571,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_struct_0(sK0)
    | ~ spl2_8
    | ~ spl2_22
    | ~ spl2_45 ),
    inference(forward_demodulation,[],[f570,f439])).

fof(f439,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_45 ),
    inference(avatar_component_clause,[],[f437])).

fof(f570,plain,
    ( k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_8
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f300,f119])).

fof(f119,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f117])).

fof(f300,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f298])).

fof(f568,plain,
    ( spl2_63
    | ~ spl2_1
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f563,f272,f75,f565])).

fof(f272,plain,
    ( spl2_21
  <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f563,plain,
    ( v2_tops_1(k1_xboole_0,sK0)
    | ~ spl2_1
    | ~ spl2_21 ),
    inference(trivial_inequality_removal,[],[f562])).

fof(f562,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v2_tops_1(k1_xboole_0,sK0)
    | ~ spl2_1
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f561,f274])).

fof(f274,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f272])).

fof(f561,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0)
    | v2_tops_1(k1_xboole_0,sK0)
    | ~ spl2_1 ),
    inference(resolution,[],[f198,f77])).

fof(f77,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f198,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | k1_xboole_0 != k1_tops_1(X1,k1_xboole_0)
      | v2_tops_1(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f56,f162])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f554,plain,
    ( spl2_61
    | ~ spl2_1
    | ~ spl2_60 ),
    inference(avatar_split_clause,[],[f552,f542,f75,f546])).

fof(f542,plain,
    ( spl2_60
  <=> v4_pre_topc(u1_struct_0(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).

fof(f552,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))
    | ~ spl2_60 ),
    inference(resolution,[],[f544,f185])).

fof(f185,plain,(
    ! [X0] :
      ( ~ v4_pre_topc(u1_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f53,f104])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f544,plain,
    ( v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl2_60 ),
    inference(avatar_component_clause,[],[f542])).

fof(f551,plain,
    ( spl2_60
    | ~ spl2_1
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f550,f209,f75,f542])).

fof(f209,plain,
    ( spl2_16
  <=> v3_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f550,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(u1_struct_0(sK0),sK0)
    | ~ spl2_16 ),
    inference(resolution,[],[f264,f211])).

fof(f211,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f209])).

fof(f264,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k1_xboole_0,X1)
      | ~ l1_pre_topc(X1)
      | v4_pre_topc(u1_struct_0(X1),X1) ) ),
    inference(forward_demodulation,[],[f257,f161])).

fof(f257,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(X1)
      | v4_pre_topc(k3_subset_1(u1_struct_0(X1),k1_xboole_0),X1)
      | ~ v3_pre_topc(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f65,f162])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).

fof(f485,plain,
    ( spl2_53
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f480,f130,f117,f482])).

fof(f130,plain,
    ( spl2_9
  <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f480,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f132,f119])).

fof(f132,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f130])).

fof(f440,plain,
    ( ~ spl2_39
    | spl2_45
    | ~ spl2_1
    | ~ spl2_37 ),
    inference(avatar_split_clause,[],[f406,f380,f75,f437,f390])).

fof(f390,plain,
    ( spl2_39
  <=> v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f380,plain,
    ( spl2_37
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f406,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_37 ),
    inference(resolution,[],[f382,f59])).

fof(f382,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f380])).

fof(f393,plain,
    ( spl2_39
    | ~ spl2_8
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f370,f217,f117,f390])).

fof(f217,plain,
    ( spl2_17
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f370,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_8
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f219,f119])).

fof(f219,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f217])).

fof(f383,plain,
    ( spl2_37
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f368,f117,f108,f380])).

fof(f108,plain,
    ( spl2_7
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f368,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(backward_demodulation,[],[f110,f119])).

fof(f110,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f108])).

fof(f301,plain,
    ( spl2_22
    | ~ spl2_20
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f282,f108,f75,f259,f298])).

fof(f259,plain,
    ( spl2_20
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f282,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_7 ),
    inference(resolution,[],[f110,f53])).

fof(f275,plain,
    ( ~ spl2_1
    | spl2_21
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f270,f203,f100,f272,f75])).

fof(f100,plain,
    ( spl2_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f203,plain,
    ( spl2_15
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f270,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_6
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f267,f205])).

fof(f205,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f203])).

fof(f267,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1))
    | ~ spl2_6 ),
    inference(resolution,[],[f72,f102])).

fof(f102,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f100])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f262,plain,
    ( ~ spl2_5
    | spl2_20
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f255,f100,f75,f259,f95])).

fof(f95,plain,
    ( spl2_5
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f255,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f65,f102])).

fof(f220,plain,
    ( spl2_17
    | ~ spl2_4
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f213,f100,f75,f90,f217])).

fof(f90,plain,
    ( spl2_4
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f213,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_tops_1(sK1,sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f55,f102])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tops_1(X1,X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).

fof(f212,plain,
    ( spl2_16
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f207,f203,f180,f209])).

fof(f180,plain,
    ( spl2_12
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f207,plain,
    ( v3_pre_topc(k1_xboole_0,sK0)
    | ~ spl2_12
    | ~ spl2_15 ),
    inference(backward_demodulation,[],[f182,f205])).

fof(f182,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f180])).

fof(f206,plain,
    ( ~ spl2_11
    | spl2_15
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f199,f100,f75,f203,f172])).

fof(f172,plain,
    ( spl2_11
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f199,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f57,f102])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f183,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f176,f100,f75,f80,f180])).

fof(f80,plain,
    ( spl2_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f176,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f71,f102])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

% (6332)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f175,plain,
    ( spl2_11
    | ~ spl2_4
    | ~ spl2_1
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f168,f100,f75,f90,f172])).

fof(f168,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_tops_1(sK1,sK0)
    | v2_tops_1(sK1,sK0)
    | ~ spl2_6 ),
    inference(resolution,[],[f54,f102])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).

fof(f133,plain,
    ( spl2_9
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f126,f100,f130])).

fof(f126,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_6 ),
    inference(resolution,[],[f70,f102])).

fof(f120,plain,
    ( spl2_8
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f113,f100,f117])).

fof(f113,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl2_6 ),
    inference(resolution,[],[f69,f102])).

fof(f111,plain,
    ( spl2_7
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f105,f100,f108])).

fof(f105,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(resolution,[],[f68,f102])).

fof(f103,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f42,f100])).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).

fof(f98,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f43,f95])).

fof(f43,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f93,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f44,f90])).

fof(f44,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    ~ spl2_3 ),
    inference(avatar_split_clause,[],[f45,f85])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f46,f80])).

fof(f46,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f47,f75])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.15/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:49:21 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.55  % (6318)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (6326)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.56  % (6327)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.56  % (6334)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (6319)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.57  % (6319)Refutation not found, incomplete strategy% (6319)------------------------------
% 0.22/0.57  % (6319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (6319)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (6319)Memory used [KB]: 10746
% 0.22/0.58  % (6319)Time elapsed: 0.127 s
% 0.22/0.58  % (6335)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.58  % (6319)------------------------------
% 0.22/0.58  % (6319)------------------------------
% 1.54/0.60  % (6327)Refutation found. Thanks to Tanya!
% 1.54/0.60  % SZS status Theorem for theBenchmark
% 1.54/0.60  % (6317)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.54/0.60  % SZS output start Proof for theBenchmark
% 1.54/0.60  fof(f803,plain,(
% 1.54/0.60    $false),
% 1.54/0.60    inference(avatar_sat_refutation,[],[f78,f83,f88,f93,f98,f103,f111,f120,f133,f175,f183,f206,f212,f220,f262,f275,f301,f383,f393,f440,f485,f551,f554,f568,f576,f644,f746,f749,f795])).
% 1.54/0.60  fof(f795,plain,(
% 1.54/0.60    spl2_3 | ~spl2_62 | ~spl2_75),
% 1.54/0.60    inference(avatar_split_clause,[],[f794,f641,f557,f85])).
% 1.54/0.60  fof(f85,plain,(
% 1.54/0.60    spl2_3 <=> k1_xboole_0 = sK1),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.54/0.60  fof(f557,plain,(
% 1.54/0.60    spl2_62 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).
% 1.54/0.60  fof(f641,plain,(
% 1.54/0.60    spl2_75 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_75])])).
% 1.54/0.60  fof(f794,plain,(
% 1.54/0.60    k1_xboole_0 = sK1 | (~spl2_62 | ~spl2_75)),
% 1.54/0.60    inference(forward_demodulation,[],[f764,f163])).
% 1.54/0.60  fof(f163,plain,(
% 1.54/0.60    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.54/0.60    inference(backward_demodulation,[],[f114,f152])).
% 1.54/0.60  fof(f152,plain,(
% 1.54/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f151,f49])).
% 1.54/0.60  fof(f49,plain,(
% 1.54/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f4])).
% 1.54/0.60  fof(f4,axiom,(
% 1.54/0.60    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.54/0.60  fof(f151,plain,(
% 1.54/0.60    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f143,f50])).
% 1.54/0.60  fof(f50,plain,(
% 1.54/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.54/0.60    inference(cnf_transformation,[],[f2])).
% 1.54/0.60  fof(f2,axiom,(
% 1.54/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.54/0.60  fof(f143,plain,(
% 1.54/0.60    ( ! [X0] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.54/0.60    inference(superposition,[],[f73,f49])).
% 1.54/0.60  fof(f73,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.54/0.60    inference(definition_unfolding,[],[f66,f67,f67])).
% 1.54/0.60  fof(f67,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f3])).
% 1.54/0.60  fof(f3,axiom,(
% 1.54/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.54/0.60  fof(f66,plain,(
% 1.54/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f1])).
% 1.54/0.60  fof(f1,axiom,(
% 1.54/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.54/0.60  fof(f114,plain,(
% 1.54/0.60    ( ! [X0] : (k3_subset_1(X0,X0) = k4_xboole_0(X0,X0)) )),
% 1.54/0.60    inference(resolution,[],[f69,f104])).
% 1.54/0.60  fof(f104,plain,(
% 1.54/0.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.54/0.60    inference(forward_demodulation,[],[f51,f48])).
% 1.54/0.60  fof(f48,plain,(
% 1.54/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.54/0.60    inference(cnf_transformation,[],[f5])).
% 1.54/0.60  fof(f5,axiom,(
% 1.54/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.54/0.60  fof(f51,plain,(
% 1.54/0.60    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f7])).
% 1.54/0.60  fof(f7,axiom,(
% 1.54/0.60    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.54/0.60  fof(f69,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f36])).
% 1.54/0.60  fof(f36,plain,(
% 1.54/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f6])).
% 1.54/0.60  fof(f6,axiom,(
% 1.54/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.54/0.60  fof(f764,plain,(
% 1.54/0.60    sK1 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl2_62 | ~spl2_75)),
% 1.54/0.60    inference(backward_demodulation,[],[f643,f558])).
% 1.54/0.60  fof(f558,plain,(
% 1.54/0.60    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl2_62),
% 1.54/0.60    inference(avatar_component_clause,[],[f557])).
% 1.54/0.60  fof(f643,plain,(
% 1.54/0.60    sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | ~spl2_75),
% 1.54/0.60    inference(avatar_component_clause,[],[f641])).
% 1.54/0.60  fof(f749,plain,(
% 1.54/0.60    ~spl2_1 | spl2_62 | ~spl2_57 | ~spl2_61),
% 1.54/0.60    inference(avatar_split_clause,[],[f748,f546,f520,f557,f75])).
% 1.54/0.60  fof(f75,plain,(
% 1.54/0.60    spl2_1 <=> l1_pre_topc(sK0)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.54/0.60  fof(f520,plain,(
% 1.54/0.60    spl2_57 <=> v1_tops_1(u1_struct_0(sK0),sK0)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 1.54/0.60  fof(f546,plain,(
% 1.54/0.60    spl2_61 <=> u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_61])])).
% 1.54/0.60  fof(f748,plain,(
% 1.54/0.60    u1_struct_0(sK0) = k2_struct_0(sK0) | ~l1_pre_topc(sK0) | (~spl2_57 | ~spl2_61)),
% 1.54/0.60    inference(forward_demodulation,[],[f747,f547])).
% 1.54/0.60  fof(f547,plain,(
% 1.54/0.60    u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | ~spl2_61),
% 1.54/0.60    inference(avatar_component_clause,[],[f546])).
% 1.54/0.60  fof(f747,plain,(
% 1.54/0.60    k2_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~spl2_57),
% 1.54/0.60    inference(resolution,[],[f522,f234])).
% 1.54/0.60  fof(f234,plain,(
% 1.54/0.60    ( ! [X0] : (~v1_tops_1(u1_struct_0(X0),X0) | k2_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0)) | ~l1_pre_topc(X0)) )),
% 1.54/0.60    inference(resolution,[],[f59,f104])).
% 1.54/0.60  fof(f59,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f31])).
% 1.54/0.60  fof(f31,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.60    inference(ennf_transformation,[],[f11])).
% 1.54/0.60  fof(f11,axiom,(
% 1.54/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 1.54/0.60  fof(f522,plain,(
% 1.54/0.60    v1_tops_1(u1_struct_0(sK0),sK0) | ~spl2_57),
% 1.54/0.60    inference(avatar_component_clause,[],[f520])).
% 1.54/0.60  fof(f746,plain,(
% 1.54/0.60    spl2_57 | ~spl2_1 | ~spl2_63),
% 1.54/0.60    inference(avatar_split_clause,[],[f745,f565,f75,f520])).
% 1.54/0.60  fof(f565,plain,(
% 1.54/0.60    spl2_63 <=> v2_tops_1(k1_xboole_0,sK0)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 1.54/0.60  fof(f745,plain,(
% 1.54/0.60    ~l1_pre_topc(sK0) | v1_tops_1(u1_struct_0(sK0),sK0) | ~spl2_63),
% 1.54/0.60    inference(resolution,[],[f744,f567])).
% 1.54/0.60  fof(f567,plain,(
% 1.54/0.60    v2_tops_1(k1_xboole_0,sK0) | ~spl2_63),
% 1.54/0.60    inference(avatar_component_clause,[],[f565])).
% 1.54/0.60  fof(f744,plain,(
% 1.54/0.60    ( ! [X1] : (~v2_tops_1(k1_xboole_0,X1) | ~l1_pre_topc(X1) | v1_tops_1(u1_struct_0(X1),X1)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f239,f161])).
% 1.54/0.60  fof(f161,plain,(
% 1.54/0.60    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.54/0.60    inference(backward_demodulation,[],[f134,f152])).
% 1.54/0.60  % (6311)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.54/0.60  fof(f134,plain,(
% 1.54/0.60    ( ! [X0] : (k3_subset_1(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.54/0.60    inference(forward_demodulation,[],[f127,f114])).
% 1.54/0.60  fof(f127,plain,(
% 1.54/0.60    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) )),
% 1.54/0.60    inference(resolution,[],[f70,f104])).
% 1.54/0.60  fof(f70,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.54/0.60    inference(cnf_transformation,[],[f37])).
% 1.54/0.60  fof(f37,plain,(
% 1.54/0.60    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f9])).
% 1.54/0.60  fof(f9,axiom,(
% 1.54/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.54/0.60  fof(f239,plain,(
% 1.54/0.60    ( ! [X1] : (~l1_pre_topc(X1) | v1_tops_1(k3_subset_1(u1_struct_0(X1),k1_xboole_0),X1) | ~v2_tops_1(k1_xboole_0,X1)) )),
% 1.54/0.60    inference(resolution,[],[f61,f162])).
% 1.54/0.60  fof(f162,plain,(
% 1.54/0.60    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.54/0.60    inference(backward_demodulation,[],[f121,f152])).
% 1.54/0.60  fof(f121,plain,(
% 1.54/0.60    ( ! [X0] : (m1_subset_1(k4_xboole_0(X0,X0),k1_zfmisc_1(X0))) )),
% 1.54/0.60    inference(backward_demodulation,[],[f106,f114])).
% 1.54/0.60  fof(f106,plain,(
% 1.54/0.60    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,X0),k1_zfmisc_1(X0))) )),
% 1.54/0.60    inference(resolution,[],[f68,f104])).
% 1.54/0.60  % (6314)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.54/0.60  fof(f68,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.54/0.60    inference(cnf_transformation,[],[f35])).
% 1.54/0.60  fof(f35,plain,(
% 1.54/0.60    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.54/0.60    inference(ennf_transformation,[],[f8])).
% 1.54/0.60  fof(f8,axiom,(
% 1.54/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.54/0.60  fof(f61,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v2_tops_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f32])).
% 1.54/0.60  fof(f32,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.60    inference(ennf_transformation,[],[f12])).
% 1.54/0.60  fof(f12,axiom,(
% 1.54/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).
% 1.54/0.60  fof(f644,plain,(
% 1.54/0.60    spl2_75 | ~spl2_53 | ~spl2_64),
% 1.54/0.60    inference(avatar_split_clause,[],[f587,f573,f482,f641])).
% 1.54/0.60  fof(f482,plain,(
% 1.54/0.60    spl2_53 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_53])])).
% 1.54/0.60  fof(f573,plain,(
% 1.54/0.60    spl2_64 <=> k4_xboole_0(u1_struct_0(sK0),sK1) = k2_struct_0(sK0)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_64])])).
% 1.54/0.60  fof(f587,plain,(
% 1.54/0.60    sK1 = k3_subset_1(u1_struct_0(sK0),k2_struct_0(sK0)) | (~spl2_53 | ~spl2_64)),
% 1.54/0.60    inference(backward_demodulation,[],[f484,f575])).
% 1.54/0.60  fof(f575,plain,(
% 1.54/0.60    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_struct_0(sK0) | ~spl2_64),
% 1.54/0.60    inference(avatar_component_clause,[],[f573])).
% 1.54/0.60  fof(f484,plain,(
% 1.54/0.60    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl2_53),
% 1.54/0.60    inference(avatar_component_clause,[],[f482])).
% 1.54/0.60  fof(f576,plain,(
% 1.54/0.60    spl2_64 | ~spl2_8 | ~spl2_22 | ~spl2_45),
% 1.54/0.60    inference(avatar_split_clause,[],[f571,f437,f298,f117,f573])).
% 1.54/0.60  fof(f117,plain,(
% 1.54/0.60    spl2_8 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.54/0.60  fof(f298,plain,(
% 1.54/0.60    spl2_22 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 1.54/0.60  fof(f437,plain,(
% 1.54/0.60    spl2_45 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_45])])).
% 1.54/0.60  fof(f571,plain,(
% 1.54/0.60    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_struct_0(sK0) | (~spl2_8 | ~spl2_22 | ~spl2_45)),
% 1.54/0.60    inference(forward_demodulation,[],[f570,f439])).
% 1.54/0.60  fof(f439,plain,(
% 1.54/0.60    k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~spl2_45),
% 1.54/0.60    inference(avatar_component_clause,[],[f437])).
% 1.54/0.60  fof(f570,plain,(
% 1.54/0.60    k4_xboole_0(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_8 | ~spl2_22)),
% 1.54/0.60    inference(forward_demodulation,[],[f300,f119])).
% 1.54/0.60  fof(f119,plain,(
% 1.54/0.60    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) | ~spl2_8),
% 1.54/0.60    inference(avatar_component_clause,[],[f117])).
% 1.54/0.60  fof(f300,plain,(
% 1.54/0.60    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_22),
% 1.54/0.60    inference(avatar_component_clause,[],[f298])).
% 1.54/0.60  fof(f568,plain,(
% 1.54/0.60    spl2_63 | ~spl2_1 | ~spl2_21),
% 1.54/0.60    inference(avatar_split_clause,[],[f563,f272,f75,f565])).
% 1.54/0.60  fof(f272,plain,(
% 1.54/0.60    spl2_21 <=> k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.54/0.60  fof(f563,plain,(
% 1.54/0.60    v2_tops_1(k1_xboole_0,sK0) | (~spl2_1 | ~spl2_21)),
% 1.54/0.60    inference(trivial_inequality_removal,[],[f562])).
% 1.54/0.60  fof(f562,plain,(
% 1.54/0.60    k1_xboole_0 != k1_xboole_0 | v2_tops_1(k1_xboole_0,sK0) | (~spl2_1 | ~spl2_21)),
% 1.54/0.60    inference(forward_demodulation,[],[f561,f274])).
% 1.54/0.60  fof(f274,plain,(
% 1.54/0.60    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~spl2_21),
% 1.54/0.60    inference(avatar_component_clause,[],[f272])).
% 1.54/0.60  fof(f561,plain,(
% 1.54/0.60    k1_xboole_0 != k1_tops_1(sK0,k1_xboole_0) | v2_tops_1(k1_xboole_0,sK0) | ~spl2_1),
% 1.54/0.60    inference(resolution,[],[f198,f77])).
% 1.54/0.60  fof(f77,plain,(
% 1.54/0.60    l1_pre_topc(sK0) | ~spl2_1),
% 1.54/0.60    inference(avatar_component_clause,[],[f75])).
% 1.54/0.60  fof(f198,plain,(
% 1.54/0.60    ( ! [X1] : (~l1_pre_topc(X1) | k1_xboole_0 != k1_tops_1(X1,k1_xboole_0) | v2_tops_1(k1_xboole_0,X1)) )),
% 1.54/0.60    inference(resolution,[],[f56,f162])).
% 1.54/0.60  fof(f56,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) )),
% 1.54/0.60    inference(cnf_transformation,[],[f30])).
% 1.54/0.60  fof(f30,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.60    inference(ennf_transformation,[],[f17])).
% 1.54/0.60  fof(f17,axiom,(
% 1.54/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 1.54/0.60  fof(f554,plain,(
% 1.54/0.60    spl2_61 | ~spl2_1 | ~spl2_60),
% 1.54/0.60    inference(avatar_split_clause,[],[f552,f542,f75,f546])).
% 1.54/0.60  fof(f542,plain,(
% 1.54/0.60    spl2_60 <=> v4_pre_topc(u1_struct_0(sK0),sK0)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_60])])).
% 1.54/0.60  fof(f552,plain,(
% 1.54/0.60    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,u1_struct_0(sK0)) | ~spl2_60),
% 1.54/0.60    inference(resolution,[],[f544,f185])).
% 1.54/0.60  fof(f185,plain,(
% 1.54/0.60    ( ! [X0] : (~v4_pre_topc(u1_struct_0(X0),X0) | ~l1_pre_topc(X0) | u1_struct_0(X0) = k2_pre_topc(X0,u1_struct_0(X0))) )),
% 1.54/0.60    inference(resolution,[],[f53,f104])).
% 1.54/0.60  fof(f53,plain,(
% 1.54/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.54/0.60    inference(cnf_transformation,[],[f25])).
% 1.54/0.60  fof(f25,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.60    inference(flattening,[],[f24])).
% 1.54/0.60  fof(f24,plain,(
% 1.54/0.60    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.60    inference(ennf_transformation,[],[f10])).
% 1.54/0.60  fof(f10,axiom,(
% 1.54/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.54/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.54/0.60  fof(f544,plain,(
% 1.54/0.60    v4_pre_topc(u1_struct_0(sK0),sK0) | ~spl2_60),
% 1.54/0.60    inference(avatar_component_clause,[],[f542])).
% 1.54/0.60  fof(f551,plain,(
% 1.54/0.60    spl2_60 | ~spl2_1 | ~spl2_16),
% 1.54/0.60    inference(avatar_split_clause,[],[f550,f209,f75,f542])).
% 1.54/0.60  fof(f209,plain,(
% 1.54/0.60    spl2_16 <=> v3_pre_topc(k1_xboole_0,sK0)),
% 1.54/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.54/0.60  fof(f550,plain,(
% 1.54/0.60    ~l1_pre_topc(sK0) | v4_pre_topc(u1_struct_0(sK0),sK0) | ~spl2_16),
% 1.54/0.60    inference(resolution,[],[f264,f211])).
% 1.54/0.60  fof(f211,plain,(
% 1.54/0.60    v3_pre_topc(k1_xboole_0,sK0) | ~spl2_16),
% 1.54/0.60    inference(avatar_component_clause,[],[f209])).
% 1.54/0.60  fof(f264,plain,(
% 1.54/0.60    ( ! [X1] : (~v3_pre_topc(k1_xboole_0,X1) | ~l1_pre_topc(X1) | v4_pre_topc(u1_struct_0(X1),X1)) )),
% 1.54/0.60    inference(forward_demodulation,[],[f257,f161])).
% 1.54/0.61  fof(f257,plain,(
% 1.54/0.61    ( ! [X1] : (~l1_pre_topc(X1) | v4_pre_topc(k3_subset_1(u1_struct_0(X1),k1_xboole_0),X1) | ~v3_pre_topc(k1_xboole_0,X1)) )),
% 1.54/0.61    inference(resolution,[],[f65,f162])).
% 1.54/0.61  fof(f65,plain,(
% 1.54/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0)) )),
% 1.54/0.61    inference(cnf_transformation,[],[f34])).
% 1.54/0.61  fof(f34,plain,(
% 1.54/0.61    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.61    inference(ennf_transformation,[],[f16])).
% 1.54/0.61  fof(f16,axiom,(
% 1.54/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.54/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tops_1)).
% 1.54/0.61  fof(f485,plain,(
% 1.54/0.61    spl2_53 | ~spl2_8 | ~spl2_9),
% 1.54/0.61    inference(avatar_split_clause,[],[f480,f130,f117,f482])).
% 1.54/0.61  fof(f130,plain,(
% 1.54/0.61    spl2_9 <=> sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 1.54/0.61  fof(f480,plain,(
% 1.54/0.61    sK1 = k3_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)) | (~spl2_8 | ~spl2_9)),
% 1.54/0.61    inference(forward_demodulation,[],[f132,f119])).
% 1.54/0.61  fof(f132,plain,(
% 1.54/0.61    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_9),
% 1.54/0.61    inference(avatar_component_clause,[],[f130])).
% 1.54/0.61  fof(f440,plain,(
% 1.54/0.61    ~spl2_39 | spl2_45 | ~spl2_1 | ~spl2_37),
% 1.54/0.61    inference(avatar_split_clause,[],[f406,f380,f75,f437,f390])).
% 1.54/0.61  fof(f390,plain,(
% 1.54/0.61    spl2_39 <=> v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 1.54/0.61  fof(f380,plain,(
% 1.54/0.61    spl2_37 <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 1.54/0.61  fof(f406,plain,(
% 1.54/0.61    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) | ~v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | ~spl2_37),
% 1.54/0.61    inference(resolution,[],[f382,f59])).
% 1.54/0.61  fof(f382,plain,(
% 1.54/0.61    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_37),
% 1.54/0.61    inference(avatar_component_clause,[],[f380])).
% 1.54/0.61  fof(f393,plain,(
% 1.54/0.61    spl2_39 | ~spl2_8 | ~spl2_17),
% 1.54/0.61    inference(avatar_split_clause,[],[f370,f217,f117,f390])).
% 1.54/0.61  fof(f217,plain,(
% 1.54/0.61    spl2_17 <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 1.54/0.61  fof(f370,plain,(
% 1.54/0.61    v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) | (~spl2_8 | ~spl2_17)),
% 1.54/0.61    inference(backward_demodulation,[],[f219,f119])).
% 1.54/0.61  fof(f219,plain,(
% 1.54/0.61    v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_17),
% 1.54/0.61    inference(avatar_component_clause,[],[f217])).
% 1.54/0.61  fof(f383,plain,(
% 1.54/0.61    spl2_37 | ~spl2_7 | ~spl2_8),
% 1.54/0.61    inference(avatar_split_clause,[],[f368,f117,f108,f380])).
% 1.54/0.61  fof(f108,plain,(
% 1.54/0.61    spl2_7 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.54/0.61  fof(f368,plain,(
% 1.54/0.61    m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_7 | ~spl2_8)),
% 1.54/0.61    inference(backward_demodulation,[],[f110,f119])).
% 1.54/0.61  fof(f110,plain,(
% 1.54/0.61    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_7),
% 1.54/0.61    inference(avatar_component_clause,[],[f108])).
% 1.54/0.61  fof(f301,plain,(
% 1.54/0.61    spl2_22 | ~spl2_20 | ~spl2_1 | ~spl2_7),
% 1.54/0.61    inference(avatar_split_clause,[],[f282,f108,f75,f259,f298])).
% 1.54/0.61  fof(f259,plain,(
% 1.54/0.61    spl2_20 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 1.54/0.61  fof(f282,plain,(
% 1.54/0.61    ~l1_pre_topc(sK0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_7),
% 1.54/0.61    inference(resolution,[],[f110,f53])).
% 1.54/0.61  fof(f275,plain,(
% 1.54/0.61    ~spl2_1 | spl2_21 | ~spl2_6 | ~spl2_15),
% 1.54/0.61    inference(avatar_split_clause,[],[f270,f203,f100,f272,f75])).
% 1.54/0.61  fof(f100,plain,(
% 1.54/0.61    spl2_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.54/0.61  fof(f203,plain,(
% 1.54/0.61    spl2_15 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.54/0.61  fof(f270,plain,(
% 1.54/0.61    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) | ~l1_pre_topc(sK0) | (~spl2_6 | ~spl2_15)),
% 1.54/0.61    inference(forward_demodulation,[],[f267,f205])).
% 1.54/0.61  fof(f205,plain,(
% 1.54/0.61    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_15),
% 1.54/0.61    inference(avatar_component_clause,[],[f203])).
% 1.54/0.61  fof(f267,plain,(
% 1.54/0.61    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK1) = k1_tops_1(sK0,k1_tops_1(sK0,sK1)) | ~spl2_6),
% 1.54/0.61    inference(resolution,[],[f72,f102])).
% 1.54/0.61  fof(f102,plain,(
% 1.54/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_6),
% 1.54/0.61    inference(avatar_component_clause,[],[f100])).
% 1.54/0.61  fof(f72,plain,(
% 1.54/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))) )),
% 1.54/0.61    inference(cnf_transformation,[],[f41])).
% 1.54/0.61  fof(f41,plain,(
% 1.54/0.61    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.54/0.61    inference(flattening,[],[f40])).
% 1.54/0.61  fof(f40,plain,(
% 1.54/0.61    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.54/0.61    inference(ennf_transformation,[],[f14])).
% 1.54/0.61  fof(f14,axiom,(
% 1.54/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 1.54/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 1.54/0.61  fof(f262,plain,(
% 1.54/0.61    ~spl2_5 | spl2_20 | ~spl2_1 | ~spl2_6),
% 1.54/0.61    inference(avatar_split_clause,[],[f255,f100,f75,f259,f95])).
% 1.54/0.61  fof(f95,plain,(
% 1.54/0.61    spl2_5 <=> v3_pre_topc(sK1,sK0)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.54/0.61  fof(f255,plain,(
% 1.54/0.61    ~l1_pre_topc(sK0) | v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v3_pre_topc(sK1,sK0) | ~spl2_6),
% 1.54/0.61    inference(resolution,[],[f65,f102])).
% 1.54/0.61  fof(f220,plain,(
% 1.54/0.61    spl2_17 | ~spl2_4 | ~spl2_1 | ~spl2_6),
% 1.54/0.61    inference(avatar_split_clause,[],[f213,f100,f75,f90,f217])).
% 1.54/0.61  fof(f90,plain,(
% 1.54/0.61    spl2_4 <=> v3_tops_1(sK1,sK0)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.54/0.61  fof(f213,plain,(
% 1.54/0.61    ~l1_pre_topc(sK0) | ~v3_tops_1(sK1,sK0) | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_6),
% 1.54/0.61    inference(resolution,[],[f55,f102])).
% 1.54/0.61  fof(f55,plain,(
% 1.54/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tops_1(X1,X0) | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 1.54/0.61    inference(cnf_transformation,[],[f29])).
% 1.54/0.61  fof(f29,plain,(
% 1.54/0.61    ! [X0] : (! [X1] : (v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.61    inference(flattening,[],[f28])).
% 1.54/0.61  fof(f28,plain,(
% 1.54/0.61    ! [X0] : (! [X1] : ((v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.61    inference(ennf_transformation,[],[f18])).
% 1.54/0.61  fof(f18,axiom,(
% 1.54/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.54/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_tops_1)).
% 1.54/0.61  fof(f212,plain,(
% 1.54/0.61    spl2_16 | ~spl2_12 | ~spl2_15),
% 1.54/0.61    inference(avatar_split_clause,[],[f207,f203,f180,f209])).
% 1.54/0.61  fof(f180,plain,(
% 1.54/0.61    spl2_12 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.54/0.61  fof(f207,plain,(
% 1.54/0.61    v3_pre_topc(k1_xboole_0,sK0) | (~spl2_12 | ~spl2_15)),
% 1.54/0.61    inference(backward_demodulation,[],[f182,f205])).
% 1.54/0.61  fof(f182,plain,(
% 1.54/0.61    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl2_12),
% 1.54/0.61    inference(avatar_component_clause,[],[f180])).
% 1.54/0.61  fof(f206,plain,(
% 1.54/0.61    ~spl2_11 | spl2_15 | ~spl2_1 | ~spl2_6),
% 1.54/0.61    inference(avatar_split_clause,[],[f199,f100,f75,f203,f172])).
% 1.54/0.61  fof(f172,plain,(
% 1.54/0.61    spl2_11 <=> v2_tops_1(sK1,sK0)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.54/0.61  fof(f199,plain,(
% 1.54/0.61    ~l1_pre_topc(sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0) | ~spl2_6),
% 1.54/0.61    inference(resolution,[],[f57,f102])).
% 1.54/0.61  fof(f57,plain,(
% 1.54/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) )),
% 1.54/0.61    inference(cnf_transformation,[],[f30])).
% 1.54/0.61  fof(f183,plain,(
% 1.54/0.61    spl2_12 | ~spl2_2 | ~spl2_1 | ~spl2_6),
% 1.54/0.61    inference(avatar_split_clause,[],[f176,f100,f75,f80,f180])).
% 1.54/0.61  fof(f80,plain,(
% 1.54/0.61    spl2_2 <=> v2_pre_topc(sK0)),
% 1.54/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.54/0.61  fof(f176,plain,(
% 1.54/0.61    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl2_6),
% 1.54/0.61    inference(resolution,[],[f71,f102])).
% 1.54/0.61  fof(f71,plain,(
% 1.54/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 1.54/0.61    inference(cnf_transformation,[],[f39])).
% 1.54/0.61  % (6332)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.54/0.61  fof(f39,plain,(
% 1.54/0.61    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.54/0.61    inference(flattening,[],[f38])).
% 1.54/0.61  fof(f38,plain,(
% 1.54/0.61    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.54/0.61    inference(ennf_transformation,[],[f13])).
% 1.54/0.61  fof(f13,axiom,(
% 1.54/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 1.54/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 1.54/0.61  fof(f175,plain,(
% 1.54/0.61    spl2_11 | ~spl2_4 | ~spl2_1 | ~spl2_6),
% 1.54/0.61    inference(avatar_split_clause,[],[f168,f100,f75,f90,f172])).
% 1.54/0.61  fof(f168,plain,(
% 1.54/0.61    ~l1_pre_topc(sK0) | ~v3_tops_1(sK1,sK0) | v2_tops_1(sK1,sK0) | ~spl2_6),
% 1.54/0.61    inference(resolution,[],[f54,f102])).
% 1.54/0.61  fof(f54,plain,(
% 1.54/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_tops_1(X1,X0) | v2_tops_1(X1,X0)) )),
% 1.54/0.61    inference(cnf_transformation,[],[f27])).
% 1.54/0.61  fof(f27,plain,(
% 1.54/0.61    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.61    inference(flattening,[],[f26])).
% 1.54/0.61  fof(f26,plain,(
% 1.54/0.61    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.54/0.61    inference(ennf_transformation,[],[f19])).
% 1.54/0.61  fof(f19,axiom,(
% 1.54/0.61    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 1.54/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_tops_1)).
% 1.54/0.61  fof(f133,plain,(
% 1.54/0.61    spl2_9 | ~spl2_6),
% 1.54/0.61    inference(avatar_split_clause,[],[f126,f100,f130])).
% 1.54/0.61  fof(f126,plain,(
% 1.54/0.61    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_6),
% 1.54/0.61    inference(resolution,[],[f70,f102])).
% 1.54/0.61  fof(f120,plain,(
% 1.54/0.61    spl2_8 | ~spl2_6),
% 1.54/0.61    inference(avatar_split_clause,[],[f113,f100,f117])).
% 1.54/0.61  fof(f113,plain,(
% 1.54/0.61    k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) | ~spl2_6),
% 1.54/0.61    inference(resolution,[],[f69,f102])).
% 1.54/0.61  fof(f111,plain,(
% 1.54/0.61    spl2_7 | ~spl2_6),
% 1.54/0.61    inference(avatar_split_clause,[],[f105,f100,f108])).
% 1.54/0.61  fof(f105,plain,(
% 1.54/0.61    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_6),
% 1.54/0.61    inference(resolution,[],[f68,f102])).
% 1.54/0.61  fof(f103,plain,(
% 1.54/0.61    spl2_6),
% 1.54/0.61    inference(avatar_split_clause,[],[f42,f100])).
% 1.54/0.61  fof(f42,plain,(
% 1.54/0.61    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.54/0.61    inference(cnf_transformation,[],[f23])).
% 1.54/0.61  fof(f23,plain,(
% 1.54/0.61    ? [X0] : (? [X1] : (k1_xboole_0 != X1 & v3_tops_1(X1,X0) & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.54/0.61    inference(flattening,[],[f22])).
% 1.54/0.61  fof(f22,plain,(
% 1.54/0.61    ? [X0] : (? [X1] : ((k1_xboole_0 != X1 & (v3_tops_1(X1,X0) & v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.54/0.61    inference(ennf_transformation,[],[f21])).
% 1.54/0.61  fof(f21,negated_conjecture,(
% 1.54/0.61    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 1.54/0.61    inference(negated_conjecture,[],[f20])).
% 1.54/0.61  fof(f20,conjecture,(
% 1.54/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tops_1(X1,X0) & v3_pre_topc(X1,X0)) => k1_xboole_0 = X1)))),
% 1.54/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_tops_1)).
% 1.54/0.61  fof(f98,plain,(
% 1.54/0.61    spl2_5),
% 1.54/0.61    inference(avatar_split_clause,[],[f43,f95])).
% 1.54/0.61  fof(f43,plain,(
% 1.54/0.61    v3_pre_topc(sK1,sK0)),
% 1.54/0.61    inference(cnf_transformation,[],[f23])).
% 1.54/0.61  fof(f93,plain,(
% 1.54/0.61    spl2_4),
% 1.54/0.61    inference(avatar_split_clause,[],[f44,f90])).
% 1.54/0.61  fof(f44,plain,(
% 1.54/0.61    v3_tops_1(sK1,sK0)),
% 1.54/0.61    inference(cnf_transformation,[],[f23])).
% 1.54/0.61  fof(f88,plain,(
% 1.54/0.61    ~spl2_3),
% 1.54/0.61    inference(avatar_split_clause,[],[f45,f85])).
% 1.54/0.61  fof(f45,plain,(
% 1.54/0.61    k1_xboole_0 != sK1),
% 1.54/0.61    inference(cnf_transformation,[],[f23])).
% 1.54/0.61  fof(f83,plain,(
% 1.54/0.61    spl2_2),
% 1.54/0.61    inference(avatar_split_clause,[],[f46,f80])).
% 1.54/0.61  fof(f46,plain,(
% 1.54/0.61    v2_pre_topc(sK0)),
% 1.54/0.61    inference(cnf_transformation,[],[f23])).
% 1.54/0.61  fof(f78,plain,(
% 1.54/0.61    spl2_1),
% 1.54/0.61    inference(avatar_split_clause,[],[f47,f75])).
% 1.54/0.61  fof(f47,plain,(
% 1.54/0.61    l1_pre_topc(sK0)),
% 1.54/0.61    inference(cnf_transformation,[],[f23])).
% 1.54/0.61  % SZS output end Proof for theBenchmark
% 1.54/0.61  % (6327)------------------------------
% 1.54/0.61  % (6327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.61  % (6327)Termination reason: Refutation
% 1.54/0.61  
% 1.54/0.61  % (6327)Memory used [KB]: 11257
% 1.54/0.61  % (6327)Time elapsed: 0.154 s
% 1.54/0.61  % (6327)------------------------------
% 1.54/0.61  % (6327)------------------------------
% 1.54/0.61  % (6333)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.54/0.61  % (6316)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.85/0.61  % (6310)Success in time 0.238 s
%------------------------------------------------------------------------------
