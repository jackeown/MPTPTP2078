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
% DateTime   : Thu Dec  3 13:12:21 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 282 expanded)
%              Number of leaves         :   33 ( 130 expanded)
%              Depth                    :    9
%              Number of atoms          :  442 (1194 expanded)
%              Number of equality atoms :   55 (  92 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f556,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f87,f92,f97,f110,f145,f151,f156,f180,f194,f195,f241,f277,f283,f352,f434,f468,f483,f535,f555])).

fof(f555,plain,
    ( ~ spl3_54
    | spl3_58 ),
    inference(avatar_contradiction_clause,[],[f554])).

fof(f554,plain,
    ( $false
    | ~ spl3_54
    | spl3_58 ),
    inference(subsumption_resolution,[],[f552,f482])).

fof(f482,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl3_54
  <=> r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f552,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_58 ),
    inference(resolution,[],[f534,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f534,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_58 ),
    inference(avatar_component_clause,[],[f532])).

fof(f532,plain,
    ( spl3_58
  <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f535,plain,
    ( ~ spl3_58
    | ~ spl3_2
    | spl3_17
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f500,f465,f153,f64,f532])).

fof(f64,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f153,plain,
    ( spl3_17
  <=> v1_tops_1(k3_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f465,plain,
    ( spl3_52
  <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f500,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | spl3_17
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f499,f66])).

fof(f66,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f499,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_17
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f498,f155])).

% (18382)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
fof(f155,plain,
    ( ~ v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f153])).

fof(f498,plain,
    ( v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_52 ),
    inference(trivial_inequality_removal,[],[f497])).

fof(f497,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_52 ),
    inference(superposition,[],[f44,f467])).

fof(f467,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f465])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) != k2_struct_0(X0)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f483,plain,
    ( spl3_54
    | ~ spl3_10
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f448,f350,f107,f480])).

fof(f107,plain,
    ( spl3_10
  <=> r1_tarski(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f350,plain,
    ( spl3_40
  <=> ! [X0] :
        ( r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f448,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | ~ spl3_10
    | ~ spl3_40 ),
    inference(resolution,[],[f351,f109])).

fof(f109,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f351,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,X0)
        | r1_tarski(k3_xboole_0(sK1,sK2),X0) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f350])).

fof(f468,plain,
    ( spl3_52
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f441,f432,f84,f69,f465])).

fof(f69,plain,
    ( spl3_3
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f84,plain,
    ( spl3_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f432,plain,
    ( spl3_49
  <=> ! [X0] :
        ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2))
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f441,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_6
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f438,f86])).

fof(f86,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f438,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | ~ spl3_49 ),
    inference(resolution,[],[f433,f71])).

fof(f71,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f433,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f432])).

fof(f434,plain,
    ( spl3_49
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_32
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f424,f280,f275,f192,f89,f79,f432])).

fof(f79,plain,
    ( spl3_5
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f89,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f192,plain,
    ( spl3_23
  <=> ! [X1] : k3_xboole_0(X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f275,plain,
    ( spl3_32
  <=> ! [X1,X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f280,plain,
    ( spl3_33
  <=> k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f424,plain,
    ( ! [X0] :
        ( k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2))
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_32
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f286,f282])).

fof(f282,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f280])).

fof(f286,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2))
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_23
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f285,f193])).

fof(f193,plain,
    ( ! [X1] : k3_xboole_0(X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f192])).

fof(f285,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) )
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f284,f91])).

fof(f91,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f89])).

fof(f284,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0)) )
    | ~ spl3_5
    | ~ spl3_32 ),
    inference(resolution,[],[f276,f81])).

fof(f81,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f79])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f275])).

fof(f352,plain,
    ( spl3_40
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f198,f187,f350])).

fof(f187,plain,
    ( spl3_22
  <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f198,plain,
    ( ! [X0] :
        ( r1_tarski(k3_xboole_0(sK1,sK2),X0)
        | ~ r1_tarski(sK2,X0) )
    | ~ spl3_22 ),
    inference(superposition,[],[f53,f189])).

fof(f189,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f187])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f283,plain,
    ( spl3_33
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f250,f239,f89,f74,f280])).

fof(f74,plain,
    ( spl3_4
  <=> v1_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f239,plain,
    ( spl3_27
  <=> ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f250,plain,
    ( k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f248,f91])).

fof(f248,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)
    | ~ spl3_4
    | ~ spl3_27 ),
    inference(resolution,[],[f240,f76])).

fof(f76,plain,
    ( v1_tops_1(sK2,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) )
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f239])).

fof(f277,plain,
    ( spl3_32
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f158,f64,f59,f275])).

fof(f59,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f157,f66])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v1_tops_1(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) )
    | ~ spl3_1 ),
    inference(resolution,[],[f46,f61])).

fof(f61,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f241,plain,
    ( spl3_27
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f141,f64,f239])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k2_struct_0(sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f43,f66])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f195,plain,
    ( spl3_22
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f183,f178,f149,f187])).

fof(f149,plain,
    ( spl3_16
  <=> ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f178,plain,
    ( spl3_21
  <=> ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f183,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1)
    | ~ spl3_16
    | ~ spl3_21 ),
    inference(superposition,[],[f150,f179])).

fof(f179,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f178])).

fof(f150,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f194,plain,
    ( spl3_23
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f185,f149,f89,f192])).

fof(f185,plain,
    ( ! [X1] : k3_xboole_0(X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1)
    | ~ spl3_7
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f129,f150])).

fof(f129,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1)
    | ~ spl3_7 ),
    inference(resolution,[],[f55,f91])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f180,plain,
    ( spl3_21
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f171,f143,f84,f178])).

fof(f143,plain,
    ( spl3_15
  <=> ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f171,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl3_6
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f128,f144])).

fof(f144,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f143])).

fof(f128,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl3_6 ),
    inference(resolution,[],[f55,f86])).

fof(f156,plain,
    ( ~ spl3_17
    | ~ spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f147,f94,f89,f153])).

fof(f94,plain,
    ( spl3_8
  <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f147,plain,
    ( ~ v1_tops_1(k3_xboole_0(sK1,sK2),sK0)
    | ~ spl3_7
    | spl3_8 ),
    inference(backward_demodulation,[],[f96,f117])).

fof(f117,plain,
    ( ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)
    | ~ spl3_7 ),
    inference(resolution,[],[f54,f91])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f96,plain,
    ( ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f151,plain,
    ( spl3_16
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f117,f89,f149])).

fof(f145,plain,
    ( spl3_15
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f116,f84,f143])).

fof(f116,plain,
    ( ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl3_6 ),
    inference(resolution,[],[f54,f86])).

fof(f110,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f99,f89,f107])).

fof(f99,plain,
    ( r1_tarski(sK2,u1_struct_0(sK0))
    | ~ spl3_7 ),
    inference(resolution,[],[f51,f91])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f97,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f41,f94])).

fof(f41,plain,(
    ~ v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f28,f27,f26])).

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

% (18381)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (18373)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (18386)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
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

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f92,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f37,f89])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f36,f84])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f82,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f40,f79])).

fof(f40,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f39,f74])).

fof(f39,plain,(
    v1_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f72,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f38,f69])).

fof(f38,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f35,f64])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f34,f59])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.49  % (18362)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (18364)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (18363)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (18384)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (18366)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (18385)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.50  % (18377)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (18371)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.51  % (18364)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (18379)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (18369)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.51  % (18387)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.51  % (18367)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (18372)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (18378)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.52  % (18370)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (18368)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.53  % (18380)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.53  % (18365)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.53  % (18383)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.53  % (18375)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.54  % (18376)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f556,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f62,f67,f72,f77,f82,f87,f92,f97,f110,f145,f151,f156,f180,f194,f195,f241,f277,f283,f352,f434,f468,f483,f535,f555])).
% 0.20/0.54  fof(f555,plain,(
% 0.20/0.54    ~spl3_54 | spl3_58),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f554])).
% 0.20/0.54  fof(f554,plain,(
% 0.20/0.54    $false | (~spl3_54 | spl3_58)),
% 0.20/0.54    inference(subsumption_resolution,[],[f552,f482])).
% 0.20/0.54  fof(f482,plain,(
% 0.20/0.54    r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0)) | ~spl3_54),
% 0.20/0.54    inference(avatar_component_clause,[],[f480])).
% 0.20/0.54  fof(f480,plain,(
% 0.20/0.54    spl3_54 <=> r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.20/0.54  fof(f552,plain,(
% 0.20/0.54    ~r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_58),
% 0.20/0.54    inference(resolution,[],[f534,f52])).
% 0.20/0.54  fof(f52,plain,(
% 0.20/0.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f33,plain,(
% 0.20/0.54    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.54    inference(nnf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,axiom,(
% 0.20/0.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.54  fof(f534,plain,(
% 0.20/0.54    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_58),
% 0.20/0.54    inference(avatar_component_clause,[],[f532])).
% 0.20/0.54  fof(f532,plain,(
% 0.20/0.54    spl3_58 <=> m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.20/0.54  fof(f535,plain,(
% 0.20/0.54    ~spl3_58 | ~spl3_2 | spl3_17 | ~spl3_52),
% 0.20/0.54    inference(avatar_split_clause,[],[f500,f465,f153,f64,f532])).
% 0.20/0.54  fof(f64,plain,(
% 0.20/0.54    spl3_2 <=> l1_pre_topc(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.54  fof(f153,plain,(
% 0.20/0.54    spl3_17 <=> v1_tops_1(k3_xboole_0(sK1,sK2),sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.54  fof(f465,plain,(
% 0.20/0.54    spl3_52 <=> k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.20/0.54  fof(f500,plain,(
% 0.20/0.54    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | spl3_17 | ~spl3_52)),
% 0.20/0.54    inference(subsumption_resolution,[],[f499,f66])).
% 0.20/0.54  fof(f66,plain,(
% 0.20/0.54    l1_pre_topc(sK0) | ~spl3_2),
% 0.20/0.54    inference(avatar_component_clause,[],[f64])).
% 0.20/0.54  fof(f499,plain,(
% 0.20/0.54    ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_17 | ~spl3_52)),
% 0.20/0.54    inference(subsumption_resolution,[],[f498,f155])).
% 0.20/0.54  % (18382)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.54  fof(f155,plain,(
% 0.20/0.54    ~v1_tops_1(k3_xboole_0(sK1,sK2),sK0) | spl3_17),
% 0.20/0.54    inference(avatar_component_clause,[],[f153])).
% 0.20/0.54  fof(f498,plain,(
% 0.20/0.54    v1_tops_1(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_52),
% 0.20/0.54    inference(trivial_inequality_removal,[],[f497])).
% 0.20/0.54  fof(f497,plain,(
% 0.20/0.54    k2_struct_0(sK0) != k2_struct_0(sK0) | v1_tops_1(k3_xboole_0(sK1,sK2),sK0) | ~m1_subset_1(k3_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_52),
% 0.20/0.54    inference(superposition,[],[f44,f467])).
% 0.20/0.54  fof(f467,plain,(
% 0.20/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~spl3_52),
% 0.20/0.54    inference(avatar_component_clause,[],[f465])).
% 0.20/0.54  fof(f44,plain,(
% 0.20/0.54    ( ! [X0,X1] : (k2_pre_topc(X0,X1) != k2_struct_0(X0) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | k2_pre_topc(X0,X1) != k2_struct_0(X0)) & (k2_pre_topc(X0,X1) = k2_struct_0(X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(nnf_transformation,[],[f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.54    inference(ennf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,axiom,(
% 0.20/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_pre_topc(X0,X1) = k2_struct_0(X0))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 0.20/0.54  fof(f483,plain,(
% 0.20/0.54    spl3_54 | ~spl3_10 | ~spl3_40),
% 0.20/0.54    inference(avatar_split_clause,[],[f448,f350,f107,f480])).
% 0.20/0.54  fof(f107,plain,(
% 0.20/0.54    spl3_10 <=> r1_tarski(sK2,u1_struct_0(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.54  fof(f350,plain,(
% 0.20/0.54    spl3_40 <=> ! [X0] : (r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~r1_tarski(sK2,X0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.20/0.54  fof(f448,plain,(
% 0.20/0.54    r1_tarski(k3_xboole_0(sK1,sK2),u1_struct_0(sK0)) | (~spl3_10 | ~spl3_40)),
% 0.20/0.54    inference(resolution,[],[f351,f109])).
% 0.20/0.54  fof(f109,plain,(
% 0.20/0.54    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_10),
% 0.20/0.54    inference(avatar_component_clause,[],[f107])).
% 0.20/0.54  fof(f351,plain,(
% 0.20/0.54    ( ! [X0] : (~r1_tarski(sK2,X0) | r1_tarski(k3_xboole_0(sK1,sK2),X0)) ) | ~spl3_40),
% 0.20/0.54    inference(avatar_component_clause,[],[f350])).
% 0.20/0.54  fof(f468,plain,(
% 0.20/0.54    spl3_52 | ~spl3_3 | ~spl3_6 | ~spl3_49),
% 0.20/0.54    inference(avatar_split_clause,[],[f441,f432,f84,f69,f465])).
% 0.20/0.54  fof(f69,plain,(
% 0.20/0.54    spl3_3 <=> v1_tops_1(sK1,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.54  fof(f84,plain,(
% 0.20/0.54    spl3_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.54  fof(f432,plain,(
% 0.20/0.54    spl3_49 <=> ! [X0] : (k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2)) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.20/0.54  fof(f441,plain,(
% 0.20/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_6 | ~spl3_49)),
% 0.20/0.54    inference(subsumption_resolution,[],[f438,f86])).
% 0.20/0.54  fof(f86,plain,(
% 0.20/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_6),
% 0.20/0.54    inference(avatar_component_clause,[],[f84])).
% 0.20/0.54  fof(f438,plain,(
% 0.20/0.54    k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | ~spl3_49)),
% 0.20/0.54    inference(resolution,[],[f433,f71])).
% 0.20/0.54  fof(f71,plain,(
% 0.20/0.54    v1_tops_1(sK1,sK0) | ~spl3_3),
% 0.20/0.54    inference(avatar_component_clause,[],[f69])).
% 0.20/0.54  fof(f433,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_49),
% 0.20/0.54    inference(avatar_component_clause,[],[f432])).
% 0.20/0.54  fof(f434,plain,(
% 0.20/0.54    spl3_49 | ~spl3_5 | ~spl3_7 | ~spl3_23 | ~spl3_32 | ~spl3_33),
% 0.20/0.54    inference(avatar_split_clause,[],[f424,f280,f275,f192,f89,f79,f432])).
% 0.20/0.54  fof(f79,plain,(
% 0.20/0.54    spl3_5 <=> v3_pre_topc(sK2,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.54  fof(f89,plain,(
% 0.20/0.54    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.54  fof(f192,plain,(
% 0.20/0.54    spl3_23 <=> ! [X1] : k3_xboole_0(X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.54  fof(f275,plain,(
% 0.20/0.54    spl3_32 <=> ! [X1,X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.54  fof(f280,plain,(
% 0.20/0.54    spl3_33 <=> k2_pre_topc(sK0,sK2) = k2_struct_0(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.54  fof(f424,plain,(
% 0.20/0.54    ( ! [X0] : (k2_struct_0(sK0) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2)) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_23 | ~spl3_32 | ~spl3_33)),
% 0.20/0.54    inference(forward_demodulation,[],[f286,f282])).
% 0.20/0.54  fof(f282,plain,(
% 0.20/0.54    k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) | ~spl3_33),
% 0.20/0.54    inference(avatar_component_clause,[],[f280])).
% 0.20/0.54  fof(f286,plain,(
% 0.20/0.54    ( ! [X0] : (k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k3_xboole_0(X0,sK2)) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_5 | ~spl3_7 | ~spl3_23 | ~spl3_32)),
% 0.20/0.54    inference(forward_demodulation,[],[f285,f193])).
% 0.20/0.54  fof(f193,plain,(
% 0.20/0.54    ( ! [X1] : (k3_xboole_0(X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1)) ) | ~spl3_23),
% 0.20/0.54    inference(avatar_component_clause,[],[f192])).
% 0.20/0.54  fof(f285,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0))) ) | (~spl3_5 | ~spl3_7 | ~spl3_32)),
% 0.20/0.54    inference(subsumption_resolution,[],[f284,f91])).
% 0.20/0.54  fof(f91,plain,(
% 0.20/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_7),
% 0.20/0.54    inference(avatar_component_clause,[],[f89])).
% 0.20/0.54  fof(f284,plain,(
% 0.20/0.54    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,X0))) ) | (~spl3_5 | ~spl3_32)),
% 0.20/0.54    inference(resolution,[],[f276,f81])).
% 0.20/0.54  fof(f81,plain,(
% 0.20/0.54    v3_pre_topc(sK2,sK0) | ~spl3_5),
% 0.20/0.54    inference(avatar_component_clause,[],[f79])).
% 0.20/0.54  fof(f276,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | ~spl3_32),
% 0.20/0.54    inference(avatar_component_clause,[],[f275])).
% 0.20/0.54  fof(f352,plain,(
% 0.20/0.54    spl3_40 | ~spl3_22),
% 0.20/0.54    inference(avatar_split_clause,[],[f198,f187,f350])).
% 0.20/0.54  fof(f187,plain,(
% 0.20/0.54    spl3_22 <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.54  fof(f198,plain,(
% 0.20/0.54    ( ! [X0] : (r1_tarski(k3_xboole_0(sK1,sK2),X0) | ~r1_tarski(sK2,X0)) ) | ~spl3_22),
% 0.20/0.54    inference(superposition,[],[f53,f189])).
% 0.20/0.54  fof(f189,plain,(
% 0.20/0.54    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1) | ~spl3_22),
% 0.20/0.54    inference(avatar_component_clause,[],[f187])).
% 0.20/0.54  fof(f53,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.20/0.54  fof(f283,plain,(
% 0.20/0.54    spl3_33 | ~spl3_4 | ~spl3_7 | ~spl3_27),
% 0.20/0.54    inference(avatar_split_clause,[],[f250,f239,f89,f74,f280])).
% 0.20/0.54  fof(f74,plain,(
% 0.20/0.54    spl3_4 <=> v1_tops_1(sK2,sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.54  fof(f239,plain,(
% 0.20/0.54    spl3_27 <=> ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0))),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.54  fof(f250,plain,(
% 0.20/0.54    k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) | (~spl3_4 | ~spl3_7 | ~spl3_27)),
% 0.20/0.54    inference(subsumption_resolution,[],[f248,f91])).
% 0.20/0.54  fof(f248,plain,(
% 0.20/0.54    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,sK2) = k2_struct_0(sK0) | (~spl3_4 | ~spl3_27)),
% 0.20/0.54    inference(resolution,[],[f240,f76])).
% 0.20/0.54  fof(f76,plain,(
% 0.20/0.54    v1_tops_1(sK2,sK0) | ~spl3_4),
% 0.20/0.54    inference(avatar_component_clause,[],[f74])).
% 0.20/0.54  fof(f240,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)) ) | ~spl3_27),
% 0.20/0.54    inference(avatar_component_clause,[],[f239])).
% 0.20/0.54  fof(f277,plain,(
% 0.20/0.54    spl3_32 | ~spl3_1 | ~spl3_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f158,f64,f59,f275])).
% 0.20/0.54  fof(f59,plain,(
% 0.20/0.54    spl3_1 <=> v2_pre_topc(sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.54  fof(f158,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | (~spl3_1 | ~spl3_2)),
% 0.20/0.54    inference(subsumption_resolution,[],[f157,f66])).
% 0.20/0.54  fof(f157,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) ) | ~spl3_1),
% 0.20/0.54    inference(resolution,[],[f46,f61])).
% 0.20/0.54  fof(f61,plain,(
% 0.20/0.54    v2_pre_topc(sK0) | ~spl3_1),
% 0.20/0.54    inference(avatar_component_clause,[],[f59])).
% 0.20/0.54  fof(f46,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))) )),
% 0.20/0.54    inference(cnf_transformation,[],[f20])).
% 0.20/0.54  fof(f20,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.54    inference(flattening,[],[f19])).
% 0.20/0.54  fof(f19,plain,(
% 0.20/0.54    ! [X0] : (! [X1] : ((! [X2] : ((k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) | ~v3_pre_topc(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f10])).
% 0.20/0.54  fof(f10,axiom,(
% 0.20/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).
% 0.20/0.54  fof(f241,plain,(
% 0.20/0.54    spl3_27 | ~spl3_2),
% 0.20/0.54    inference(avatar_split_clause,[],[f141,f64,f239])).
% 0.20/0.54  fof(f141,plain,(
% 0.20/0.54    ( ! [X0] : (~v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k2_struct_0(sK0)) ) | ~spl3_2),
% 0.20/0.54    inference(resolution,[],[f43,f66])).
% 0.20/0.54  fof(f43,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k2_struct_0(X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f30])).
% 0.20/0.54  fof(f195,plain,(
% 0.20/0.54    spl3_22 | ~spl3_16 | ~spl3_21),
% 0.20/0.54    inference(avatar_split_clause,[],[f183,f178,f149,f187])).
% 0.20/0.54  fof(f149,plain,(
% 0.20/0.54    spl3_16 <=> ! [X1] : k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.54  fof(f178,plain,(
% 0.20/0.54    spl3_21 <=> ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.54  fof(f183,plain,(
% 0.20/0.54    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,sK1) | (~spl3_16 | ~spl3_21)),
% 0.20/0.54    inference(superposition,[],[f150,f179])).
% 0.20/0.54  fof(f179,plain,(
% 0.20/0.54    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl3_21),
% 0.20/0.54    inference(avatar_component_clause,[],[f178])).
% 0.20/0.54  fof(f150,plain,(
% 0.20/0.54    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)) ) | ~spl3_16),
% 0.20/0.54    inference(avatar_component_clause,[],[f149])).
% 0.20/0.54  fof(f194,plain,(
% 0.20/0.54    spl3_23 | ~spl3_7 | ~spl3_16),
% 0.20/0.54    inference(avatar_split_clause,[],[f185,f149,f89,f192])).
% 0.20/0.54  fof(f185,plain,(
% 0.20/0.54    ( ! [X1] : (k3_xboole_0(X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1)) ) | (~spl3_7 | ~spl3_16)),
% 0.20/0.54    inference(forward_demodulation,[],[f129,f150])).
% 0.20/0.54  fof(f129,plain,(
% 0.20/0.54    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k9_subset_1(u1_struct_0(sK0),sK2,X1)) ) | ~spl3_7),
% 0.20/0.54    inference(resolution,[],[f55,f91])).
% 0.20/0.54  fof(f55,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.20/0.54  fof(f180,plain,(
% 0.20/0.54    spl3_21 | ~spl3_6 | ~spl3_15),
% 0.20/0.54    inference(avatar_split_clause,[],[f171,f143,f84,f178])).
% 0.20/0.54  fof(f143,plain,(
% 0.20/0.54    spl3_15 <=> ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.54  fof(f171,plain,(
% 0.20/0.54    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | (~spl3_6 | ~spl3_15)),
% 0.20/0.54    inference(forward_demodulation,[],[f128,f144])).
% 0.20/0.54  fof(f144,plain,(
% 0.20/0.54    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)) ) | ~spl3_15),
% 0.20/0.54    inference(avatar_component_clause,[],[f143])).
% 0.20/0.54  fof(f128,plain,(
% 0.20/0.54    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl3_6),
% 0.20/0.54    inference(resolution,[],[f55,f86])).
% 0.20/0.54  fof(f156,plain,(
% 0.20/0.54    ~spl3_17 | ~spl3_7 | spl3_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f147,f94,f89,f153])).
% 0.20/0.54  fof(f94,plain,(
% 0.20/0.54    spl3_8 <=> v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.54  fof(f147,plain,(
% 0.20/0.54    ~v1_tops_1(k3_xboole_0(sK1,sK2),sK0) | (~spl3_7 | spl3_8)),
% 0.20/0.54    inference(backward_demodulation,[],[f96,f117])).
% 0.20/0.54  fof(f117,plain,(
% 0.20/0.54    ( ! [X1] : (k9_subset_1(u1_struct_0(sK0),X1,sK2) = k3_xboole_0(X1,sK2)) ) | ~spl3_7),
% 0.20/0.54    inference(resolution,[],[f54,f91])).
% 0.20/0.54  fof(f54,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f4])).
% 0.20/0.54  fof(f4,axiom,(
% 0.20/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.54  fof(f96,plain,(
% 0.20/0.54    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_8),
% 0.20/0.54    inference(avatar_component_clause,[],[f94])).
% 0.20/0.54  fof(f151,plain,(
% 0.20/0.54    spl3_16 | ~spl3_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f117,f89,f149])).
% 0.20/0.54  fof(f145,plain,(
% 0.20/0.54    spl3_15 | ~spl3_6),
% 0.20/0.54    inference(avatar_split_clause,[],[f116,f84,f143])).
% 0.20/0.54  fof(f116,plain,(
% 0.20/0.54    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1)) ) | ~spl3_6),
% 0.20/0.54    inference(resolution,[],[f54,f86])).
% 0.20/0.54  fof(f110,plain,(
% 0.20/0.54    spl3_10 | ~spl3_7),
% 0.20/0.54    inference(avatar_split_clause,[],[f99,f89,f107])).
% 0.20/0.54  fof(f99,plain,(
% 0.20/0.54    r1_tarski(sK2,u1_struct_0(sK0)) | ~spl3_7),
% 0.20/0.54    inference(resolution,[],[f51,f91])).
% 0.20/0.54  fof(f51,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f33])).
% 0.20/0.54  fof(f97,plain,(
% 0.20/0.54    ~spl3_8),
% 0.20/0.54    inference(avatar_split_clause,[],[f41,f94])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 0.20/0.54    inference(cnf_transformation,[],[f29])).
% 0.20/0.54  fof(f29,plain,(
% 0.20/0.54    ((~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f28,f27,f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    ? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.54    introduced(choice_axiom,[])).
% 0.20/0.54  % (18381)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.54  % (18373)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.54  % (18386)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.55  fof(f28,plain,(
% 0.20/0.55    ? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v3_pre_topc(X2,sK0) & v1_tops_1(X2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v1_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v3_pre_topc(sK2,sK0) & v1_tops_1(sK2,sK0) & v1_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.55    introduced(choice_axiom,[])).
% 0.20/0.55  fof(f14,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : (~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f13])).
% 0.20/0.55  fof(f13,plain,(
% 0.20/0.55    ? [X0] : (? [X1] : (? [X2] : ((~v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f12])).
% 0.20/0.55  fof(f12,negated_conjecture,(
% 0.20/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.55    inference(negated_conjecture,[],[f11])).
% 0.20/0.55  fof(f11,conjecture,(
% 0.20/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & v1_tops_1(X2,X0) & v1_tops_1(X1,X0)) => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 0.20/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).
% 0.20/0.55  fof(f92,plain,(
% 0.20/0.55    spl3_7),
% 0.20/0.55    inference(avatar_split_clause,[],[f37,f89])).
% 0.20/0.55  fof(f37,plain,(
% 0.20/0.55    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f87,plain,(
% 0.20/0.55    spl3_6),
% 0.20/0.55    inference(avatar_split_clause,[],[f36,f84])).
% 0.20/0.55  fof(f36,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f82,plain,(
% 0.20/0.55    spl3_5),
% 0.20/0.55    inference(avatar_split_clause,[],[f40,f79])).
% 0.20/0.55  fof(f40,plain,(
% 0.20/0.55    v3_pre_topc(sK2,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f77,plain,(
% 0.20/0.55    spl3_4),
% 0.20/0.55    inference(avatar_split_clause,[],[f39,f74])).
% 0.20/0.55  fof(f39,plain,(
% 0.20/0.55    v1_tops_1(sK2,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f72,plain,(
% 0.20/0.55    spl3_3),
% 0.20/0.55    inference(avatar_split_clause,[],[f38,f69])).
% 0.20/0.55  fof(f38,plain,(
% 0.20/0.55    v1_tops_1(sK1,sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f67,plain,(
% 0.20/0.55    spl3_2),
% 0.20/0.55    inference(avatar_split_clause,[],[f35,f64])).
% 0.20/0.55  fof(f35,plain,(
% 0.20/0.55    l1_pre_topc(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  fof(f62,plain,(
% 0.20/0.55    spl3_1),
% 0.20/0.55    inference(avatar_split_clause,[],[f34,f59])).
% 0.20/0.55  fof(f34,plain,(
% 0.20/0.55    v2_pre_topc(sK0)),
% 0.20/0.55    inference(cnf_transformation,[],[f29])).
% 0.20/0.55  % SZS output end Proof for theBenchmark
% 0.20/0.55  % (18364)------------------------------
% 0.20/0.55  % (18364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (18364)Termination reason: Refutation
% 0.20/0.55  
% 0.20/0.55  % (18364)Memory used [KB]: 6524
% 0.20/0.55  % (18364)Time elapsed: 0.103 s
% 0.20/0.55  % (18364)------------------------------
% 0.20/0.55  % (18364)------------------------------
% 0.20/0.55  % (18361)Success in time 0.186 s
%------------------------------------------------------------------------------
