%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 272 expanded)
%              Number of leaves         :   35 ( 127 expanded)
%              Depth                    :   10
%              Number of atoms          :  417 (1139 expanded)
%              Number of equality atoms :   39 (  72 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f460,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f83,f88,f93,f99,f105,f114,f119,f148,f160,f165,f175,f201,f213,f287,f289,f444,f457,f459])).

fof(f459,plain,
    ( ~ spl3_28
    | spl3_38 ),
    inference(avatar_split_clause,[],[f458,f454,f251])).

fof(f251,plain,
    ( spl3_28
  <=> r1_tarski(k3_xboole_0(sK1,sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f454,plain,
    ( spl3_38
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f458,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),k2_struct_0(sK0))
    | spl3_38 ),
    inference(resolution,[],[f456,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f456,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0)))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f454])).

fof(f457,plain,
    ( ~ spl3_7
    | spl3_25
    | ~ spl3_38
    | ~ spl3_10
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f452,f441,f102,f454,f210,f85])).

fof(f85,plain,
    ( spl3_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f210,plain,
    ( spl3_25
  <=> v1_tops_1(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f102,plain,
    ( spl3_10
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f441,plain,
    ( spl3_36
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f452,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_10
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f451,f104])).

fof(f104,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f451,plain,
    ( v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_36 ),
    inference(trivial_inequality_removal,[],[f450])).

fof(f450,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_36 ),
    inference(superposition,[],[f45,f443])).

fof(f443,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f441])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_struct_0(X0) != k2_pre_topc(X0,X1) )
            & ( k2_struct_0(X0) = k2_pre_topc(X0,X1)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f444,plain,
    ( ~ spl3_4
    | spl3_36
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f436,f172,f162,f116,f112,f102,f441,f70])).

fof(f70,plain,
    ( spl3_4
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f112,plain,
    ( spl3_11
  <=> ! [X0] :
        ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f116,plain,
    ( spl3_12
  <=> k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f162,plain,
    ( spl3_19
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f172,plain,
    ( spl3_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f436,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ v1_tops_1(sK1,sK0)
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_19
    | ~ spl3_21 ),
    inference(resolution,[],[f433,f164])).

fof(f164,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f162])).

fof(f433,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
        | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2))
        | ~ v1_tops_1(X0,sK0) )
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f432,f104])).

fof(f432,plain,
    ( ! [X0] :
        ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0) )
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f431,f118])).

fof(f118,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f431,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0) )
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f430,f305])).

fof(f305,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),sK2,X0) = k3_xboole_0(X0,sK2)
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f189,f190])).

fof(f190,plain,
    ( ! [X1] : k9_subset_1(k2_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)
    | ~ spl3_21 ),
    inference(resolution,[],[f174,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f174,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f172])).

fof(f189,plain,
    ( ! [X0] : k9_subset_1(k2_struct_0(sK0),X0,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X0)
    | ~ spl3_21 ),
    inference(resolution,[],[f174,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f430,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0) )
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f113,f104])).

fof(f113,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f289,plain,(
    spl3_33 ),
    inference(avatar_contradiction_clause,[],[f288])).

fof(f288,plain,
    ( $false
    | spl3_33 ),
    inference(resolution,[],[f286,f47])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f286,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl3_33
  <=> r1_tarski(k3_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f287,plain,
    ( ~ spl3_33
    | ~ spl3_18
    | spl3_28 ),
    inference(avatar_split_clause,[],[f271,f251,f157,f284])).

fof(f157,plain,
    ( spl3_18
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f271,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),sK1)
    | ~ spl3_18
    | spl3_28 ),
    inference(resolution,[],[f252,f184])).

fof(f184,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_struct_0(sK0))
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_18 ),
    inference(resolution,[],[f159,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

% (15434)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f159,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f157])).

fof(f252,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),k2_struct_0(sK0))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f251])).

fof(f213,plain,
    ( ~ spl3_25
    | ~ spl3_21
    | spl3_24 ),
    inference(avatar_split_clause,[],[f208,f198,f172,f210])).

fof(f198,plain,
    ( spl3_24
  <=> v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f208,plain,
    ( ~ v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_21
    | spl3_24 ),
    inference(backward_demodulation,[],[f200,f190])).

fof(f200,plain,
    ( ~ v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)
    | spl3_24 ),
    inference(avatar_component_clause,[],[f198])).

fof(f201,plain,
    ( ~ spl3_24
    | spl3_1
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f196,f102,f55,f198])).

fof(f55,plain,
    ( spl3_1
  <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f196,plain,
    ( ~ v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f57,f104])).

fof(f57,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f175,plain,
    ( spl3_21
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f153,f102,f75,f172])).

fof(f75,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f153,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f77,f104])).

fof(f77,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f165,plain,
    ( spl3_19
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f151,f102,f80,f162])).

fof(f80,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f151,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f82,f104])).

fof(f82,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f160,plain,
    ( spl3_18
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f150,f145,f102,f157])).

fof(f145,plain,
    ( spl3_17
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f150,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl3_10
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f147,f104])).

fof(f147,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f145])).

fof(f148,plain,
    ( spl3_17
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f130,f80,f145])).

fof(f130,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(resolution,[],[f82,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f119,plain,
    ( ~ spl3_7
    | spl3_12
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f107,f75,f65,f116,f85])).

fof(f65,plain,
    ( spl3_3
  <=> v1_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f107,plain,
    ( ~ v1_tops_1(sK2,sK0)
    | k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(resolution,[],[f77,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f114,plain,
    ( ~ spl3_8
    | ~ spl3_7
    | spl3_11
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f106,f75,f60,f112,f85,f90])).

fof(f90,plain,
    ( spl3_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f60,plain,
    ( spl3_2
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(sK2,sK0)
        | k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0))
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f77,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

fof(f105,plain,
    ( spl3_10
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f100,f96,f102])).

fof(f96,plain,
    ( spl3_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f100,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f98,f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f98,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f96])).

fof(f99,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f94,f85,f96])).

fof(f94,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_7 ),
    inference(resolution,[],[f87,f43])).

fof(f43,plain,(
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

fof(f87,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f85])).

fof(f93,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f32,f90])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v3_pre_topc(sK2,sK0)
    & v1_tops_1(sK2,sK0)
    & v1_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v3_pre_topc(X2,X0)
                & v1_tops_1(X2,X0)
                & v1_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v3_pre_topc(X2,sK0)
              & v1_tops_1(X2,sK0)
              & v1_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v3_pre_topc(X2,sK0)
            & v1_tops_1(X2,sK0)
            & v1_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v3_pre_topc(X2,sK0)
          & v1_tops_1(X2,sK0)
          & v1_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v3_pre_topc(X2,sK0)
        & v1_tops_1(X2,sK0)
        & v1_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v3_pre_topc(sK2,sK0)
      & v1_tops_1(sK2,sK0)
      & v1_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v3_pre_topc(X2,X0)
              & v1_tops_1(X2,X0)
              & v1_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & v1_tops_1(X2,X0)
                    & v1_tops_1(X1,X0) )
                 => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v1_tops_1(X2,X0)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).

fof(f88,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f33,f85])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f83,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f34,f80])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f73,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f36,f70])).

fof(f36,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f68,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f37,f65])).

fof(f37,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f38,f60])).

fof(f38,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f39,f55])).

fof(f39,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:03:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (15439)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.46  % (15427)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (15429)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (15435)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (15433)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.47  % (15440)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (15431)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (15442)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.48  % (15437)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (15432)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (15438)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (15430)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (15428)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (15437)Refutation found. Thanks to Tanya!
% 0.22/0.50  % SZS status Theorem for theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f460,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f58,f63,f68,f73,f78,f83,f88,f93,f99,f105,f114,f119,f148,f160,f165,f175,f201,f213,f287,f289,f444,f457,f459])).
% 0.22/0.50  fof(f459,plain,(
% 0.22/0.50    ~spl3_28 | spl3_38),
% 0.22/0.50    inference(avatar_split_clause,[],[f458,f454,f251])).
% 0.22/0.50  fof(f251,plain,(
% 0.22/0.50    spl3_28 <=> r1_tarski(k3_xboole_0(sK1,sK2),k2_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.50  fof(f454,plain,(
% 0.22/0.50    spl3_38 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.22/0.50  fof(f458,plain,(
% 0.22/0.50    ~r1_tarski(k3_xboole_0(sK1,sK2),k2_struct_0(sK0)) | spl3_38),
% 0.22/0.50    inference(resolution,[],[f456,f50])).
% 0.22/0.50  fof(f50,plain,(
% 0.22/0.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f31,plain,(
% 0.22/0.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.50    inference(nnf_transformation,[],[f8])).
% 0.22/0.50  fof(f8,axiom,(
% 0.22/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.50  fof(f456,plain,(
% 0.22/0.50    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) | spl3_38),
% 0.22/0.50    inference(avatar_component_clause,[],[f454])).
% 0.22/0.50  fof(f457,plain,(
% 0.22/0.50    ~spl3_7 | spl3_25 | ~spl3_38 | ~spl3_10 | ~spl3_36),
% 0.22/0.50    inference(avatar_split_clause,[],[f452,f441,f102,f454,f210,f85])).
% 0.22/0.50  fof(f85,plain,(
% 0.22/0.50    spl3_7 <=> l1_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.50  fof(f210,plain,(
% 0.22/0.50    spl3_25 <=> v1_tops_1(k3_xboole_0(sK1,sK2),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.22/0.50  fof(f102,plain,(
% 0.22/0.50    spl3_10 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.50  fof(f441,plain,(
% 0.22/0.50    spl3_36 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.22/0.50  fof(f452,plain,(
% 0.22/0.50    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k3_xboole_0(sK1,sK2),sK0) | ~l1_pre_topc(sK0) | (~spl3_10 | ~spl3_36)),
% 0.22/0.50    inference(forward_demodulation,[],[f451,f104])).
% 0.22/0.50  fof(f104,plain,(
% 0.22/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_10),
% 0.22/0.50    inference(avatar_component_clause,[],[f102])).
% 0.22/0.50  fof(f451,plain,(
% 0.22/0.50    v1_tops_1(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_36),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f450])).
% 0.22/0.50  fof(f450,plain,(
% 0.22/0.50    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_36),
% 0.22/0.50    inference(superposition,[],[f45,f443])).
% 0.22/0.50  fof(f443,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_36),
% 0.22/0.50    inference(avatar_component_clause,[],[f441])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k2_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f30,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_struct_0(X0) != k2_pre_topc(X0,X1)) & (k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(nnf_transformation,[],[f19])).
% 0.22/0.50  fof(f19,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f11])).
% 0.22/0.50  fof(f11,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.22/0.50  fof(f444,plain,(
% 0.22/0.50    ~spl3_4 | spl3_36 | ~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_19 | ~spl3_21),
% 0.22/0.50    inference(avatar_split_clause,[],[f436,f172,f162,f116,f112,f102,f441,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    spl3_4 <=> v1_tops_1(sK1,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.50  fof(f112,plain,(
% 0.22/0.50    spl3_11 <=> ! [X0] : (k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.50  fof(f116,plain,(
% 0.22/0.50    spl3_12 <=> k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.50  fof(f162,plain,(
% 0.22/0.50    spl3_19 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.50  fof(f172,plain,(
% 0.22/0.50    spl3_21 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.50  fof(f436,plain,(
% 0.22/0.50    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~v1_tops_1(sK1,sK0) | (~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_19 | ~spl3_21)),
% 0.22/0.50    inference(resolution,[],[f433,f164])).
% 0.22/0.50  fof(f164,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_19),
% 0.22/0.50    inference(avatar_component_clause,[],[f162])).
% 0.22/0.50  fof(f433,plain,(
% 0.22/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2)) | ~v1_tops_1(X0,sK0)) ) | (~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_21)),
% 0.22/0.50    inference(forward_demodulation,[],[f432,f104])).
% 0.22/0.50  fof(f432,plain,(
% 0.22/0.50    ( ! [X0] : (k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0)) ) | (~spl3_10 | ~spl3_11 | ~spl3_12 | ~spl3_21)),
% 0.22/0.50    inference(forward_demodulation,[],[f431,f118])).
% 0.22/0.50  fof(f118,plain,(
% 0.22/0.50    k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) | ~spl3_12),
% 0.22/0.50    inference(avatar_component_clause,[],[f116])).
% 0.22/0.50  fof(f431,plain,(
% 0.22/0.50    ( ! [X0] : (k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0)) ) | (~spl3_10 | ~spl3_11 | ~spl3_21)),
% 0.22/0.50    inference(forward_demodulation,[],[f430,f305])).
% 0.22/0.50  fof(f305,plain,(
% 0.22/0.50    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),sK2,X0) = k3_xboole_0(X0,sK2)) ) | ~spl3_21),
% 0.22/0.50    inference(forward_demodulation,[],[f189,f190])).
% 0.22/0.50  fof(f190,plain,(
% 0.22/0.50    ( ! [X1] : (k9_subset_1(k2_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)) ) | ~spl3_21),
% 0.22/0.50    inference(resolution,[],[f174,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f22])).
% 0.22/0.50  fof(f22,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f6])).
% 0.22/0.50  fof(f6,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.22/0.50  fof(f174,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | ~spl3_21),
% 0.22/0.50    inference(avatar_component_clause,[],[f172])).
% 0.22/0.50  fof(f189,plain,(
% 0.22/0.50    ( ! [X0] : (k9_subset_1(k2_struct_0(sK0),X0,sK2) = k9_subset_1(k2_struct_0(sK0),sK2,X0)) ) | ~spl3_21),
% 0.22/0.50    inference(resolution,[],[f174,f52])).
% 0.22/0.50  fof(f52,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f23])).
% 0.22/0.50  fof(f23,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f3])).
% 0.22/0.50  fof(f3,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.22/0.50  fof(f430,plain,(
% 0.22/0.50    ( ! [X0] : (k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0)) ) | (~spl3_10 | ~spl3_11)),
% 0.22/0.50    inference(forward_demodulation,[],[f113,f104])).
% 0.22/0.50  fof(f113,plain,(
% 0.22/0.50    ( ! [X0] : (k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0)) ) | ~spl3_11),
% 0.22/0.50    inference(avatar_component_clause,[],[f112])).
% 0.22/0.50  fof(f289,plain,(
% 0.22/0.50    spl3_33),
% 0.22/0.50    inference(avatar_contradiction_clause,[],[f288])).
% 0.22/0.50  fof(f288,plain,(
% 0.22/0.50    $false | spl3_33),
% 0.22/0.50    inference(resolution,[],[f286,f47])).
% 0.22/0.50  fof(f47,plain,(
% 0.22/0.50    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f1])).
% 0.22/0.50  fof(f1,axiom,(
% 0.22/0.50    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.50  fof(f286,plain,(
% 0.22/0.50    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | spl3_33),
% 0.22/0.50    inference(avatar_component_clause,[],[f284])).
% 0.22/0.50  fof(f284,plain,(
% 0.22/0.50    spl3_33 <=> r1_tarski(k3_xboole_0(sK1,sK2),sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.50  fof(f287,plain,(
% 0.22/0.50    ~spl3_33 | ~spl3_18 | spl3_28),
% 0.22/0.50    inference(avatar_split_clause,[],[f271,f251,f157,f284])).
% 0.22/0.50  fof(f157,plain,(
% 0.22/0.50    spl3_18 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.50  fof(f271,plain,(
% 0.22/0.50    ~r1_tarski(k3_xboole_0(sK1,sK2),sK1) | (~spl3_18 | spl3_28)),
% 0.22/0.50    inference(resolution,[],[f252,f184])).
% 0.22/0.50  fof(f184,plain,(
% 0.22/0.50    ( ! [X0] : (r1_tarski(X0,k2_struct_0(sK0)) | ~r1_tarski(X0,sK1)) ) | ~spl3_18),
% 0.22/0.50    inference(resolution,[],[f159,f53])).
% 0.22/0.50  fof(f53,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f25])).
% 0.22/0.50  fof(f25,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.50    inference(flattening,[],[f24])).
% 0.22/0.50  fof(f24,plain,(
% 0.22/0.50    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.50    inference(ennf_transformation,[],[f2])).
% 0.22/0.50  fof(f2,axiom,(
% 0.22/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.50  % (15434)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  fof(f159,plain,(
% 0.22/0.50    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl3_18),
% 0.22/0.50    inference(avatar_component_clause,[],[f157])).
% 0.22/0.50  fof(f252,plain,(
% 0.22/0.50    ~r1_tarski(k3_xboole_0(sK1,sK2),k2_struct_0(sK0)) | spl3_28),
% 0.22/0.50    inference(avatar_component_clause,[],[f251])).
% 0.22/0.50  fof(f213,plain,(
% 0.22/0.50    ~spl3_25 | ~spl3_21 | spl3_24),
% 0.22/0.50    inference(avatar_split_clause,[],[f208,f198,f172,f210])).
% 0.22/0.50  fof(f198,plain,(
% 0.22/0.50    spl3_24 <=> v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.50  fof(f208,plain,(
% 0.22/0.50    ~v1_tops_1(k3_xboole_0(sK1,sK2),sK0) | (~spl3_21 | spl3_24)),
% 0.22/0.50    inference(backward_demodulation,[],[f200,f190])).
% 0.22/0.50  fof(f200,plain,(
% 0.22/0.50    ~v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) | spl3_24),
% 0.22/0.50    inference(avatar_component_clause,[],[f198])).
% 0.22/0.50  fof(f201,plain,(
% 0.22/0.50    ~spl3_24 | spl3_1 | ~spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f196,f102,f55,f198])).
% 0.22/0.50  fof(f55,plain,(
% 0.22/0.50    spl3_1 <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.50  fof(f196,plain,(
% 0.22/0.50    ~v1_tops_1(k9_subset_1(k2_struct_0(sK0),sK1,sK2),sK0) | (spl3_1 | ~spl3_10)),
% 0.22/0.50    inference(forward_demodulation,[],[f57,f104])).
% 0.22/0.50  fof(f57,plain,(
% 0.22/0.50    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_1),
% 0.22/0.50    inference(avatar_component_clause,[],[f55])).
% 0.22/0.50  fof(f175,plain,(
% 0.22/0.50    spl3_21 | ~spl3_5 | ~spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f153,f102,f75,f172])).
% 0.22/0.50  fof(f75,plain,(
% 0.22/0.50    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.50  fof(f153,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_5 | ~spl3_10)),
% 0.22/0.50    inference(backward_demodulation,[],[f77,f104])).
% 0.22/0.50  fof(f77,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 0.22/0.50    inference(avatar_component_clause,[],[f75])).
% 0.22/0.50  fof(f165,plain,(
% 0.22/0.50    spl3_19 | ~spl3_6 | ~spl3_10),
% 0.22/0.50    inference(avatar_split_clause,[],[f151,f102,f80,f162])).
% 0.22/0.50  fof(f80,plain,(
% 0.22/0.50    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.50  fof(f151,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | (~spl3_6 | ~spl3_10)),
% 0.22/0.50    inference(backward_demodulation,[],[f82,f104])).
% 0.22/0.50  fof(f82,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.22/0.50    inference(avatar_component_clause,[],[f80])).
% 0.22/0.50  fof(f160,plain,(
% 0.22/0.50    spl3_18 | ~spl3_10 | ~spl3_17),
% 0.22/0.50    inference(avatar_split_clause,[],[f150,f145,f102,f157])).
% 0.22/0.50  fof(f145,plain,(
% 0.22/0.50    spl3_17 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.50  fof(f150,plain,(
% 0.22/0.50    r1_tarski(sK1,k2_struct_0(sK0)) | (~spl3_10 | ~spl3_17)),
% 0.22/0.50    inference(backward_demodulation,[],[f147,f104])).
% 0.22/0.50  fof(f147,plain,(
% 0.22/0.50    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_17),
% 0.22/0.50    inference(avatar_component_clause,[],[f145])).
% 0.22/0.50  fof(f148,plain,(
% 0.22/0.50    spl3_17 | ~spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f130,f80,f145])).
% 0.22/0.50  fof(f130,plain,(
% 0.22/0.50    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 0.22/0.50    inference(resolution,[],[f82,f49])).
% 0.22/0.50  fof(f49,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f31])).
% 0.22/0.50  fof(f119,plain,(
% 0.22/0.50    ~spl3_7 | spl3_12 | ~spl3_3 | ~spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f107,f75,f65,f116,f85])).
% 0.22/0.50  fof(f65,plain,(
% 0.22/0.50    spl3_3 <=> v1_tops_1(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.50  fof(f107,plain,(
% 0.22/0.50    ~v1_tops_1(sK2,sK0) | k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~spl3_5),
% 0.22/0.50    inference(resolution,[],[f77,f44])).
% 0.22/0.50  fof(f44,plain,(
% 0.22/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f30])).
% 0.22/0.50  fof(f114,plain,(
% 0.22/0.50    ~spl3_8 | ~spl3_7 | spl3_11 | ~spl3_2 | ~spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f106,f75,f60,f112,f85,f90])).
% 0.22/0.50  fof(f90,plain,(
% 0.22/0.50    spl3_8 <=> v2_pre_topc(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.50  fof(f60,plain,(
% 0.22/0.50    spl3_2 <=> v3_pre_topc(sK2,sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.50  fof(f106,plain,(
% 0.22/0.50    ( ! [X0] : (~v3_pre_topc(sK2,sK0) | k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl3_5),
% 0.22/0.50    inference(resolution,[],[f77,f46])).
% 0.22/0.50  fof(f46,plain,(
% 0.22/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f21])).
% 0.22/0.50  fof(f21,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f20])).
% 0.22/0.50  fof(f20,plain,(
% 0.22/0.50    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f12])).
% 0.22/0.50  fof(f12,axiom,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).
% 0.22/0.50  fof(f105,plain,(
% 0.22/0.50    spl3_10 | ~spl3_9),
% 0.22/0.50    inference(avatar_split_clause,[],[f100,f96,f102])).
% 0.22/0.50  fof(f96,plain,(
% 0.22/0.50    spl3_9 <=> l1_struct_0(sK0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.50  fof(f100,plain,(
% 0.22/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.22/0.50    inference(resolution,[],[f98,f42])).
% 0.22/0.50  fof(f42,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f17])).
% 0.22/0.50  fof(f17,plain,(
% 0.22/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.50  fof(f98,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl3_9),
% 0.22/0.50    inference(avatar_component_clause,[],[f96])).
% 0.22/0.50  fof(f99,plain,(
% 0.22/0.50    spl3_9 | ~spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f94,f85,f96])).
% 0.22/0.50  fof(f94,plain,(
% 0.22/0.50    l1_struct_0(sK0) | ~spl3_7),
% 0.22/0.50    inference(resolution,[],[f87,f43])).
% 0.22/0.50  fof(f43,plain,(
% 0.22/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f18])).
% 0.22/0.50  fof(f18,plain,(
% 0.22/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.50    inference(ennf_transformation,[],[f10])).
% 0.22/0.50  fof(f10,axiom,(
% 0.22/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.50  fof(f87,plain,(
% 0.22/0.50    l1_pre_topc(sK0) | ~spl3_7),
% 0.22/0.50    inference(avatar_component_clause,[],[f85])).
% 0.22/0.50  fof(f93,plain,(
% 0.22/0.50    spl3_8),
% 0.22/0.50    inference(avatar_split_clause,[],[f32,f90])).
% 0.22/0.50  fof(f32,plain,(
% 0.22/0.50    v2_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.22/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f16,f28,f27,f26])).
% 0.22/0.50  fof(f26,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f27,plain,(
% 0.22/0.50    ? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f28,plain,(
% 0.22/0.50    ? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.50    introduced(choice_axiom,[])).
% 0.22/0.50  fof(f16,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.50    inference(flattening,[],[f15])).
% 0.22/0.50  fof(f15,plain,(
% 0.22/0.50    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.50    inference(ennf_transformation,[],[f14])).
% 0.22/0.50  fof(f14,negated_conjecture,(
% 0.22/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.50    inference(negated_conjecture,[],[f13])).
% 0.22/0.50  fof(f13,conjecture,(
% 0.22/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.22/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).
% 0.22/0.50  fof(f88,plain,(
% 0.22/0.50    spl3_7),
% 0.22/0.50    inference(avatar_split_clause,[],[f33,f85])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    l1_pre_topc(sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f83,plain,(
% 0.22/0.50    spl3_6),
% 0.22/0.50    inference(avatar_split_clause,[],[f34,f80])).
% 0.22/0.50  fof(f34,plain,(
% 0.22/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f78,plain,(
% 0.22/0.50    spl3_5),
% 0.22/0.50    inference(avatar_split_clause,[],[f35,f75])).
% 0.22/0.50  fof(f35,plain,(
% 0.22/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f73,plain,(
% 0.22/0.50    spl3_4),
% 0.22/0.50    inference(avatar_split_clause,[],[f36,f70])).
% 0.22/0.50  fof(f36,plain,(
% 0.22/0.50    v1_tops_1(sK1,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl3_3),
% 0.22/0.50    inference(avatar_split_clause,[],[f37,f65])).
% 0.22/0.50  fof(f37,plain,(
% 0.22/0.50    v1_tops_1(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f63,plain,(
% 0.22/0.50    spl3_2),
% 0.22/0.50    inference(avatar_split_clause,[],[f38,f60])).
% 0.22/0.50  fof(f38,plain,(
% 0.22/0.50    v3_pre_topc(sK2,sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f58,plain,(
% 0.22/0.50    ~spl3_1),
% 0.22/0.50    inference(avatar_split_clause,[],[f39,f55])).
% 0.22/0.50  fof(f39,plain,(
% 0.22/0.50    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  % SZS output end Proof for theBenchmark
% 0.22/0.50  % (15437)------------------------------
% 0.22/0.50  % (15437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (15437)Termination reason: Refutation
% 0.22/0.50  
% 0.22/0.50  % (15437)Memory used [KB]: 10874
% 0.22/0.50  % (15437)Time elapsed: 0.075 s
% 0.22/0.50  % (15437)------------------------------
% 0.22/0.50  % (15437)------------------------------
% 0.22/0.51  % (15423)Success in time 0.144 s
%------------------------------------------------------------------------------
