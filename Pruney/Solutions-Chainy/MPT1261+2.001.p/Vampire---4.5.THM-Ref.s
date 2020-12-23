%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:47 EST 2020

% Result     : Theorem 2.44s
% Output     : Refutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  162 ( 330 expanded)
%              Number of leaves         :   33 ( 126 expanded)
%              Depth                    :   13
%              Number of atoms          :  451 ( 843 expanded)
%              Number of equality atoms :   84 ( 173 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2592,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f103,f108,f120,f134,f161,f181,f190,f207,f280,f411,f427,f437,f442,f463,f501,f514,f1760,f1774,f2583,f2591])).

fof(f2591,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4
    | ~ spl3_115 ),
    inference(avatar_contradiction_clause,[],[f2590])).

fof(f2590,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_3
    | spl3_4
    | ~ spl3_115 ),
    inference(subsumption_resolution,[],[f2589,f119])).

fof(f119,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f2589,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_4
    | ~ spl3_115 ),
    inference(subsumption_resolution,[],[f2587,f128])).

fof(f128,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl3_4
  <=> v4_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f2587,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_115 ),
    inference(superposition,[],[f110,f2582])).

fof(f2582,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_115 ),
    inference(avatar_component_clause,[],[f2580])).

fof(f2580,plain,
    ( spl3_115
  <=> sK1 = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_115])])).

fof(f110,plain,
    ( ! [X0] :
        ( v4_pre_topc(k2_pre_topc(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f109,f107])).

fof(f107,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(k2_pre_topc(sK0,X0),sK0) )
    | ~ spl3_1 ),
    inference(resolution,[],[f102,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f102,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2583,plain,
    ( spl3_115
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_73
    | ~ spl3_75 ),
    inference(avatar_split_clause,[],[f2420,f1771,f1757,f439,f187,f2580])).

fof(f187,plain,
    ( spl3_11
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f439,plain,
    ( spl3_33
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f1757,plain,
    ( spl3_73
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f1771,plain,
    ( spl3_75
  <=> k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f2420,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_73
    | ~ spl3_75 ),
    inference(subsumption_resolution,[],[f2419,f441])).

fof(f441,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f439])).

fof(f2419,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ spl3_11
    | ~ spl3_73
    | ~ spl3_75 ),
    inference(forward_demodulation,[],[f2418,f1759])).

fof(f1759,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f1757])).

fof(f2418,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl3_11
    | ~ spl3_73
    | ~ spl3_75 ),
    inference(forward_demodulation,[],[f2417,f1773])).

fof(f1773,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f1771])).

fof(f2417,plain,
    ( sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl3_11
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f2416,f65])).

fof(f65,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f2416,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_subset_1(sK1)
    | ~ m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl3_11
    | ~ spl3_73 ),
    inference(forward_demodulation,[],[f2415,f1759])).

fof(f2415,plain,
    ( k2_subset_1(sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f2413,f189])).

fof(f189,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f187])).

fof(f2413,plain,
    ( k2_subset_1(sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_11 ),
    inference(superposition,[],[f526,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f526,plain,
    ( ! [X0] :
        ( k2_xboole_0(k2_tops_1(sK0,sK1),X0) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK1)) )
    | ~ spl3_11 ),
    inference(resolution,[],[f189,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f1774,plain,
    ( spl3_75
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f559,f434,f408,f117,f105,f1771])).

fof(f408,plain,
    ( spl3_29
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f434,plain,
    ( spl3_32
  <=> k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f559,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f422,f558])).

fof(f558,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f556,f119])).

fof(f556,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_32 ),
    inference(superposition,[],[f436,f114])).

fof(f114,plain,
    ( ! [X3] :
        ( k2_pre_topc(sK0,X3) = k4_subset_1(u1_struct_0(sK0),X3,k2_tops_1(sK0,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f107,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f436,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f434])).

fof(f422,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f420,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f420,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_29 ),
    inference(superposition,[],[f79,f410])).

fof(f410,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f408])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1760,plain,
    ( spl3_73
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f511,f439,f277,f187,f117,f1757])).

fof(f277,plain,
    ( spl3_20
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f511,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_33 ),
    inference(backward_demodulation,[],[f496,f510])).

fof(f510,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_33 ),
    inference(backward_demodulation,[],[f456,f304])).

fof(f304,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(backward_demodulation,[],[f196,f303])).

fof(f303,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(subsumption_resolution,[],[f301,f119])).

fof(f301,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_20 ),
    inference(superposition,[],[f279,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f279,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f277])).

fof(f196,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f194,f195])).

fof(f195,plain,
    ( k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_11 ),
    inference(resolution,[],[f189,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f194,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1)))
    | ~ spl3_11 ),
    inference(resolution,[],[f189,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f456,plain,
    ( k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_33 ),
    inference(resolution,[],[f441,f81])).

fof(f496,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f455,f456])).

fof(f455,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1)))
    | ~ spl3_33 ),
    inference(resolution,[],[f441,f82])).

fof(f514,plain,
    ( ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f135,f131,f127])).

fof(f131,plain,
    ( spl3_5
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f135,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f61,f133])).

fof(f133,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f61,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v4_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).

fof(f501,plain,
    ( ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f500])).

fof(f500,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10 ),
    inference(subsumption_resolution,[],[f499,f179])).

fof(f179,plain,
    ( ~ r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f178])).

fof(f178,plain,
    ( spl3_10
  <=> r1_tarski(k2_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f499,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f498,f119])).

fof(f498,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f129,f112])).

fof(f112,plain,
    ( ! [X1] :
        ( ~ v4_pre_topc(X1,sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_tarski(k2_tops_1(sK0,X1),X1) )
    | ~ spl3_2 ),
    inference(resolution,[],[f107,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | r1_tarski(k2_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_tops_1(X0,X1),X1)
          | ~ v4_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => r1_tarski(k2_tops_1(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).

fof(f129,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f127])).

fof(f463,plain,
    ( ~ spl3_3
    | spl3_5
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_33 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | ~ spl3_3
    | spl3_5
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f461,f119])).

fof(f461,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3
    | spl3_5
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f340,f458])).

fof(f458,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_20
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f456,f304])).

fof(f340,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_5 ),
    inference(superposition,[],[f132,f94])).

fof(f132,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f131])).

fof(f442,plain,
    ( spl3_33
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f432,f424,f439])).

fof(f424,plain,
    ( spl3_31
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f432,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_31 ),
    inference(resolution,[],[f426,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f426,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f424])).

fof(f437,plain,
    ( spl3_32
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f217,f204,f117,f434])).

fof(f204,plain,
    ( spl3_12
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f217,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(resolution,[],[f206,f121])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(sK1,X0) = k4_subset_1(u1_struct_0(sK0),sK1,X0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f119,f98])).

fof(f206,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f204])).

fof(f427,plain,
    ( spl3_31
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f421,f408,f424])).

fof(f421,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_29 ),
    inference(superposition,[],[f72,f410])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f411,plain,
    ( spl3_29
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f303,f277,f117,f408])).

fof(f280,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f209,f117,f105,f277])).

fof(f209,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f113,f119])).

fof(f113,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X2) = k7_subset_1(u1_struct_0(sK0),X2,k2_tops_1(sK0,X2)) )
    | ~ spl3_2 ),
    inference(resolution,[],[f107,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f207,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f185,f117,f105,f204])).

fof(f185,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(resolution,[],[f111,f119])).

fof(f111,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_2 ),
    inference(resolution,[],[f107,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f190,plain,
    ( spl3_11
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f183,f178,f187])).

fof(f183,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ spl3_10 ),
    inference(resolution,[],[f180,f91])).

fof(f180,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f178])).

fof(f181,plain,
    ( spl3_10
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f175,f158,f178])).

fof(f158,plain,
    ( spl3_9
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f175,plain,
    ( r1_tarski(k2_tops_1(sK0,sK1),sK1)
    | ~ spl3_9 ),
    inference(superposition,[],[f72,f160])).

fof(f160,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f158])).

fof(f161,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f139,f131,f117,f158])).

fof(f139,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f137,f119])).

fof(f137,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(superposition,[],[f133,f94])).

fof(f134,plain,
    ( spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f60,f131,f127])).

fof(f60,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f120,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f62,f117])).

fof(f62,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f36])).

fof(f108,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f64,f105])).

fof(f64,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f103,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f63,f100])).

fof(f63,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:22:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.22/0.49  % (9134)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.51  % (9129)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (9150)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.52  % (9142)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (9154)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.53  % (9160)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.53  % (9145)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (9136)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (9135)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (9152)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.43/0.54  % (9130)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.43/0.54  % (9137)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.43/0.54  % (9147)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.43/0.54  % (9138)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.43/0.54  % (9141)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.43/0.54  % (9148)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.43/0.54  % (9161)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.43/0.55  % (9144)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.55  % (9132)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.43/0.55  % (9140)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.43/0.55  % (9151)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.43/0.55  % (9159)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.43/0.55  % (9139)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.43/0.55  % (9143)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.43/0.55  % (9158)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.58/0.56  % (9149)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.58/0.56  % (9157)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.58/0.56  % (9133)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.58/0.56  % (9155)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.58/0.57  % (9153)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 2.44/0.72  % (9151)Refutation found. Thanks to Tanya!
% 2.44/0.72  % SZS status Theorem for theBenchmark
% 2.44/0.72  % SZS output start Proof for theBenchmark
% 2.44/0.72  fof(f2592,plain,(
% 2.44/0.72    $false),
% 2.44/0.72    inference(avatar_sat_refutation,[],[f103,f108,f120,f134,f161,f181,f190,f207,f280,f411,f427,f437,f442,f463,f501,f514,f1760,f1774,f2583,f2591])).
% 2.44/0.72  fof(f2591,plain,(
% 2.44/0.72    ~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_4 | ~spl3_115),
% 2.44/0.72    inference(avatar_contradiction_clause,[],[f2590])).
% 2.44/0.72  fof(f2590,plain,(
% 2.44/0.72    $false | (~spl3_1 | ~spl3_2 | ~spl3_3 | spl3_4 | ~spl3_115)),
% 2.44/0.72    inference(subsumption_resolution,[],[f2589,f119])).
% 2.44/0.72  fof(f119,plain,(
% 2.44/0.72    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.44/0.72    inference(avatar_component_clause,[],[f117])).
% 2.44/0.72  fof(f117,plain,(
% 2.44/0.72    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.44/0.72  fof(f2589,plain,(
% 2.44/0.72    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2 | spl3_4 | ~spl3_115)),
% 2.44/0.72    inference(subsumption_resolution,[],[f2587,f128])).
% 2.44/0.72  fof(f128,plain,(
% 2.44/0.72    ~v4_pre_topc(sK1,sK0) | spl3_4),
% 2.44/0.72    inference(avatar_component_clause,[],[f127])).
% 2.44/0.72  fof(f127,plain,(
% 2.44/0.72    spl3_4 <=> v4_pre_topc(sK1,sK0)),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.44/0.72  fof(f2587,plain,(
% 2.44/0.72    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_1 | ~spl3_2 | ~spl3_115)),
% 2.44/0.72    inference(superposition,[],[f110,f2582])).
% 2.44/0.72  fof(f2582,plain,(
% 2.44/0.72    sK1 = k2_pre_topc(sK0,sK1) | ~spl3_115),
% 2.44/0.72    inference(avatar_component_clause,[],[f2580])).
% 2.44/0.72  fof(f2580,plain,(
% 2.44/0.72    spl3_115 <=> sK1 = k2_pre_topc(sK0,sK1)),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_115])])).
% 2.44/0.72  fof(f110,plain,(
% 2.44/0.72    ( ! [X0] : (v4_pre_topc(k2_pre_topc(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_1 | ~spl3_2)),
% 2.44/0.72    inference(subsumption_resolution,[],[f109,f107])).
% 2.44/0.72  fof(f107,plain,(
% 2.44/0.72    l1_pre_topc(sK0) | ~spl3_2),
% 2.44/0.72    inference(avatar_component_clause,[],[f105])).
% 2.44/0.72  fof(f105,plain,(
% 2.44/0.72    spl3_2 <=> l1_pre_topc(sK0)),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.44/0.72  fof(f109,plain,(
% 2.44/0.72    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k2_pre_topc(sK0,X0),sK0)) ) | ~spl3_1),
% 2.44/0.72    inference(resolution,[],[f102,f86])).
% 2.44/0.72  fof(f86,plain,(
% 2.44/0.72    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 2.44/0.72    inference(cnf_transformation,[],[f49])).
% 2.44/0.72  fof(f49,plain,(
% 2.44/0.72    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.44/0.72    inference(flattening,[],[f48])).
% 2.44/0.72  fof(f48,plain,(
% 2.44/0.72    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.44/0.72    inference(ennf_transformation,[],[f27])).
% 2.44/0.72  fof(f27,axiom,(
% 2.44/0.72    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tops_1)).
% 2.44/0.72  fof(f102,plain,(
% 2.44/0.72    v2_pre_topc(sK0) | ~spl3_1),
% 2.44/0.72    inference(avatar_component_clause,[],[f100])).
% 2.44/0.72  fof(f100,plain,(
% 2.44/0.72    spl3_1 <=> v2_pre_topc(sK0)),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.44/0.72  fof(f2583,plain,(
% 2.44/0.72    spl3_115 | ~spl3_11 | ~spl3_33 | ~spl3_73 | ~spl3_75),
% 2.44/0.72    inference(avatar_split_clause,[],[f2420,f1771,f1757,f439,f187,f2580])).
% 2.44/0.72  fof(f187,plain,(
% 2.44/0.72    spl3_11 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.44/0.72  fof(f439,plain,(
% 2.44/0.72    spl3_33 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1))),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 2.44/0.72  fof(f1757,plain,(
% 2.44/0.72    spl3_73 <=> k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1))),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 2.44/0.72  fof(f1771,plain,(
% 2.44/0.72    spl3_75 <=> k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1)),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 2.44/0.72  fof(f2420,plain,(
% 2.44/0.72    sK1 = k2_pre_topc(sK0,sK1) | (~spl3_11 | ~spl3_33 | ~spl3_73 | ~spl3_75)),
% 2.44/0.72    inference(subsumption_resolution,[],[f2419,f441])).
% 2.44/0.72  fof(f441,plain,(
% 2.44/0.72    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl3_33),
% 2.44/0.72    inference(avatar_component_clause,[],[f439])).
% 2.44/0.72  fof(f2419,plain,(
% 2.44/0.72    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | sK1 = k2_pre_topc(sK0,sK1) | (~spl3_11 | ~spl3_73 | ~spl3_75)),
% 2.44/0.72    inference(forward_demodulation,[],[f2418,f1759])).
% 2.44/0.72  fof(f1759,plain,(
% 2.44/0.72    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | ~spl3_73),
% 2.44/0.72    inference(avatar_component_clause,[],[f1757])).
% 2.44/0.72  fof(f2418,plain,(
% 2.44/0.72    sK1 = k2_pre_topc(sK0,sK1) | ~m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | (~spl3_11 | ~spl3_73 | ~spl3_75)),
% 2.44/0.72    inference(forward_demodulation,[],[f2417,f1773])).
% 2.44/0.72  fof(f1773,plain,(
% 2.44/0.72    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) | ~spl3_75),
% 2.44/0.72    inference(avatar_component_clause,[],[f1771])).
% 2.44/0.72  fof(f2417,plain,(
% 2.44/0.72    sK1 = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | (~spl3_11 | ~spl3_73)),
% 2.44/0.72    inference(forward_demodulation,[],[f2416,f65])).
% 2.44/0.72  fof(f65,plain,(
% 2.44/0.72    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 2.44/0.72    inference(cnf_transformation,[],[f16])).
% 2.44/0.72  fof(f16,axiom,(
% 2.44/0.72    ! [X0] : k2_subset_1(X0) = X0),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 2.44/0.72  fof(f2416,plain,(
% 2.44/0.72    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_subset_1(sK1) | ~m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | (~spl3_11 | ~spl3_73)),
% 2.44/0.72    inference(forward_demodulation,[],[f2415,f1759])).
% 2.44/0.72  fof(f2415,plain,(
% 2.44/0.72    k2_subset_1(sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~spl3_11),
% 2.44/0.72    inference(subsumption_resolution,[],[f2413,f189])).
% 2.44/0.72  fof(f189,plain,(
% 2.44/0.72    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl3_11),
% 2.44/0.72    inference(avatar_component_clause,[],[f187])).
% 2.44/0.72  fof(f2413,plain,(
% 2.44/0.72    k2_subset_1(sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~m1_subset_1(k3_subset_1(sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl3_11),
% 2.44/0.72    inference(superposition,[],[f526,f83])).
% 2.44/0.72  fof(f83,plain,(
% 2.44/0.72    ( ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.44/0.72    inference(cnf_transformation,[],[f45])).
% 2.44/0.72  fof(f45,plain,(
% 2.44/0.72    ! [X0,X1] : (k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.44/0.72    inference(ennf_transformation,[],[f23])).
% 2.44/0.72  fof(f23,axiom,(
% 2.44/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 2.44/0.72  fof(f526,plain,(
% 2.44/0.72    ( ! [X0] : (k2_xboole_0(k2_tops_1(sK0,sK1),X0) = k4_subset_1(sK1,k2_tops_1(sK0,sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK1))) ) | ~spl3_11),
% 2.44/0.72    inference(resolution,[],[f189,f98])).
% 2.44/0.72  fof(f98,plain,(
% 2.44/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 2.44/0.72    inference(cnf_transformation,[],[f59])).
% 2.44/0.72  fof(f59,plain,(
% 2.44/0.72    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.44/0.72    inference(flattening,[],[f58])).
% 2.44/0.72  fof(f58,plain,(
% 2.44/0.72    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.44/0.72    inference(ennf_transformation,[],[f21])).
% 2.44/0.72  fof(f21,axiom,(
% 2.44/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.44/0.72  fof(f1774,plain,(
% 2.44/0.72    spl3_75 | ~spl3_2 | ~spl3_3 | ~spl3_29 | ~spl3_32),
% 2.44/0.72    inference(avatar_split_clause,[],[f559,f434,f408,f117,f105,f1771])).
% 2.44/0.72  fof(f408,plain,(
% 2.44/0.72    spl3_29 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.44/0.72  fof(f434,plain,(
% 2.44/0.72    spl3_32 <=> k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.44/0.72  fof(f559,plain,(
% 2.44/0.72    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_29 | ~spl3_32)),
% 2.44/0.72    inference(backward_demodulation,[],[f422,f558])).
% 2.44/0.72  fof(f558,plain,(
% 2.44/0.72    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) | (~spl3_2 | ~spl3_3 | ~spl3_32)),
% 2.44/0.72    inference(subsumption_resolution,[],[f556,f119])).
% 2.44/0.72  fof(f556,plain,(
% 2.44/0.72    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_32)),
% 2.44/0.72    inference(superposition,[],[f436,f114])).
% 2.44/0.72  fof(f114,plain,(
% 2.44/0.72    ( ! [X3] : (k2_pre_topc(sK0,X3) = k4_subset_1(u1_struct_0(sK0),X3,k2_tops_1(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 2.44/0.72    inference(resolution,[],[f107,f68])).
% 2.44/0.72  fof(f68,plain,(
% 2.44/0.72    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.44/0.72    inference(cnf_transformation,[],[f38])).
% 2.44/0.72  fof(f38,plain,(
% 2.44/0.72    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.44/0.72    inference(ennf_transformation,[],[f29])).
% 2.44/0.72  fof(f29,axiom,(
% 2.44/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.44/0.72  fof(f436,plain,(
% 2.44/0.72    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_32),
% 2.44/0.72    inference(avatar_component_clause,[],[f434])).
% 2.44/0.72  fof(f422,plain,(
% 2.44/0.72    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_29),
% 2.44/0.72    inference(forward_demodulation,[],[f420,f74])).
% 2.44/0.72  fof(f74,plain,(
% 2.44/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.44/0.72    inference(cnf_transformation,[],[f1])).
% 2.44/0.72  fof(f1,axiom,(
% 2.44/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.44/0.72  fof(f420,plain,(
% 2.44/0.72    k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),sK1) | ~spl3_29),
% 2.44/0.72    inference(superposition,[],[f79,f410])).
% 2.44/0.72  fof(f410,plain,(
% 2.44/0.72    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_29),
% 2.44/0.72    inference(avatar_component_clause,[],[f408])).
% 2.44/0.72  fof(f79,plain,(
% 2.44/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.44/0.72    inference(cnf_transformation,[],[f10])).
% 2.44/0.72  fof(f10,axiom,(
% 2.44/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.44/0.72  fof(f1760,plain,(
% 2.44/0.72    spl3_73 | ~spl3_3 | ~spl3_11 | ~spl3_20 | ~spl3_33),
% 2.44/0.72    inference(avatar_split_clause,[],[f511,f439,f277,f187,f117,f1757])).
% 2.44/0.72  fof(f277,plain,(
% 2.44/0.72    spl3_20 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.44/0.72  fof(f511,plain,(
% 2.44/0.72    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k2_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_11 | ~spl3_20 | ~spl3_33)),
% 2.44/0.72    inference(backward_demodulation,[],[f496,f510])).
% 2.44/0.72  fof(f510,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_11 | ~spl3_20 | ~spl3_33)),
% 2.44/0.72    inference(backward_demodulation,[],[f456,f304])).
% 2.44/0.72  fof(f304,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_11 | ~spl3_20)),
% 2.44/0.72    inference(backward_demodulation,[],[f196,f303])).
% 2.44/0.72  fof(f303,plain,(
% 2.44/0.72    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_20)),
% 2.44/0.72    inference(subsumption_resolution,[],[f301,f119])).
% 2.44/0.72  fof(f301,plain,(
% 2.44/0.72    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_20),
% 2.44/0.72    inference(superposition,[],[f279,f94])).
% 2.44/0.72  fof(f94,plain,(
% 2.44/0.72    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.44/0.72    inference(cnf_transformation,[],[f53])).
% 2.44/0.72  fof(f53,plain,(
% 2.44/0.72    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.44/0.72    inference(ennf_transformation,[],[f22])).
% 2.44/0.72  fof(f22,axiom,(
% 2.44/0.72    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.44/0.72  fof(f279,plain,(
% 2.44/0.72    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_20),
% 2.44/0.72    inference(avatar_component_clause,[],[f277])).
% 2.44/0.72  fof(f196,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k4_xboole_0(sK1,k2_tops_1(sK0,sK1))) | ~spl3_11),
% 2.44/0.72    inference(backward_demodulation,[],[f194,f195])).
% 2.44/0.72  fof(f195,plain,(
% 2.44/0.72    k3_subset_1(sK1,k2_tops_1(sK0,sK1)) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_11),
% 2.44/0.72    inference(resolution,[],[f189,f81])).
% 2.44/0.72  fof(f81,plain,(
% 2.44/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.44/0.72    inference(cnf_transformation,[],[f43])).
% 2.44/0.72  fof(f43,plain,(
% 2.44/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.44/0.72    inference(ennf_transformation,[],[f17])).
% 2.44/0.72  fof(f17,axiom,(
% 2.44/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.44/0.72  fof(f194,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k2_tops_1(sK0,sK1))) | ~spl3_11),
% 2.44/0.72    inference(resolution,[],[f189,f82])).
% 2.44/0.72  fof(f82,plain,(
% 2.44/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.44/0.72    inference(cnf_transformation,[],[f44])).
% 2.44/0.72  fof(f44,plain,(
% 2.44/0.72    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.44/0.72    inference(ennf_transformation,[],[f19])).
% 2.44/0.72  fof(f19,axiom,(
% 2.44/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.44/0.72  fof(f456,plain,(
% 2.44/0.72    k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) = k3_subset_1(sK1,k1_tops_1(sK0,sK1)) | ~spl3_33),
% 2.44/0.72    inference(resolution,[],[f441,f81])).
% 2.44/0.72  fof(f496,plain,(
% 2.44/0.72    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k4_xboole_0(sK1,k1_tops_1(sK0,sK1))) | ~spl3_33),
% 2.44/0.72    inference(forward_demodulation,[],[f455,f456])).
% 2.44/0.72  fof(f455,plain,(
% 2.44/0.72    k1_tops_1(sK0,sK1) = k3_subset_1(sK1,k3_subset_1(sK1,k1_tops_1(sK0,sK1))) | ~spl3_33),
% 2.44/0.72    inference(resolution,[],[f441,f82])).
% 2.44/0.72  fof(f514,plain,(
% 2.44/0.72    ~spl3_4 | ~spl3_5),
% 2.44/0.72    inference(avatar_split_clause,[],[f135,f131,f127])).
% 2.44/0.72  fof(f131,plain,(
% 2.44/0.72    spl3_5 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.44/0.72  fof(f135,plain,(
% 2.44/0.72    ~v4_pre_topc(sK1,sK0) | ~spl3_5),
% 2.44/0.72    inference(subsumption_resolution,[],[f61,f133])).
% 2.44/0.72  fof(f133,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~spl3_5),
% 2.44/0.72    inference(avatar_component_clause,[],[f131])).
% 2.44/0.72  fof(f61,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~v4_pre_topc(sK1,sK0)),
% 2.44/0.72    inference(cnf_transformation,[],[f36])).
% 2.44/0.72  fof(f36,plain,(
% 2.44/0.72    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.44/0.72    inference(flattening,[],[f35])).
% 2.44/0.72  fof(f35,plain,(
% 2.44/0.72    ? [X0] : (? [X1] : ((v4_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.44/0.72    inference(ennf_transformation,[],[f33])).
% 2.44/0.72  fof(f33,negated_conjecture,(
% 2.44/0.72    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.44/0.72    inference(negated_conjecture,[],[f32])).
% 2.44/0.72  fof(f32,conjecture,(
% 2.44/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k1_tops_1(X0,X1)))))),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_tops_1)).
% 2.44/0.72  fof(f501,plain,(
% 2.44/0.72    ~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_10),
% 2.44/0.72    inference(avatar_contradiction_clause,[],[f500])).
% 2.44/0.72  fof(f500,plain,(
% 2.44/0.72    $false | (~spl3_2 | ~spl3_3 | ~spl3_4 | spl3_10)),
% 2.44/0.72    inference(subsumption_resolution,[],[f499,f179])).
% 2.44/0.72  fof(f179,plain,(
% 2.44/0.72    ~r1_tarski(k2_tops_1(sK0,sK1),sK1) | spl3_10),
% 2.44/0.72    inference(avatar_component_clause,[],[f178])).
% 2.44/0.72  fof(f178,plain,(
% 2.44/0.72    spl3_10 <=> r1_tarski(k2_tops_1(sK0,sK1),sK1)),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.44/0.72  fof(f499,plain,(
% 2.44/0.72    r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl3_2 | ~spl3_3 | ~spl3_4)),
% 2.44/0.72    inference(subsumption_resolution,[],[f498,f119])).
% 2.44/0.72  fof(f498,plain,(
% 2.44/0.72    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tops_1(sK0,sK1),sK1) | (~spl3_2 | ~spl3_4)),
% 2.44/0.72    inference(resolution,[],[f129,f112])).
% 2.44/0.72  fof(f112,plain,(
% 2.44/0.72    ( ! [X1] : (~v4_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k2_tops_1(sK0,X1),X1)) ) | ~spl3_2),
% 2.44/0.72    inference(resolution,[],[f107,f70])).
% 2.44/0.72  fof(f70,plain,(
% 2.44/0.72    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | r1_tarski(k2_tops_1(X0,X1),X1)) )),
% 2.44/0.72    inference(cnf_transformation,[],[f41])).
% 2.44/0.72  fof(f41,plain,(
% 2.44/0.72    ! [X0] : (! [X1] : (r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.44/0.72    inference(flattening,[],[f40])).
% 2.44/0.72  fof(f40,plain,(
% 2.44/0.72    ! [X0] : (! [X1] : ((r1_tarski(k2_tops_1(X0,X1),X1) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.44/0.72    inference(ennf_transformation,[],[f30])).
% 2.44/0.72  fof(f30,axiom,(
% 2.44/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => r1_tarski(k2_tops_1(X0,X1),X1))))),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_tops_1)).
% 2.44/0.72  fof(f129,plain,(
% 2.44/0.72    v4_pre_topc(sK1,sK0) | ~spl3_4),
% 2.44/0.72    inference(avatar_component_clause,[],[f127])).
% 2.44/0.72  fof(f463,plain,(
% 2.44/0.72    ~spl3_3 | spl3_5 | ~spl3_11 | ~spl3_20 | ~spl3_33),
% 2.44/0.72    inference(avatar_contradiction_clause,[],[f462])).
% 2.44/0.72  fof(f462,plain,(
% 2.44/0.72    $false | (~spl3_3 | spl3_5 | ~spl3_11 | ~spl3_20 | ~spl3_33)),
% 2.44/0.72    inference(subsumption_resolution,[],[f461,f119])).
% 2.44/0.72  fof(f461,plain,(
% 2.44/0.72    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_3 | spl3_5 | ~spl3_11 | ~spl3_20 | ~spl3_33)),
% 2.44/0.72    inference(subsumption_resolution,[],[f340,f458])).
% 2.44/0.72  fof(f458,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_11 | ~spl3_20 | ~spl3_33)),
% 2.44/0.72    inference(forward_demodulation,[],[f456,f304])).
% 2.44/0.72  fof(f340,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) != k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_5),
% 2.44/0.72    inference(superposition,[],[f132,f94])).
% 2.44/0.72  fof(f132,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | spl3_5),
% 2.44/0.72    inference(avatar_component_clause,[],[f131])).
% 2.44/0.72  fof(f442,plain,(
% 2.44/0.72    spl3_33 | ~spl3_31),
% 2.44/0.72    inference(avatar_split_clause,[],[f432,f424,f439])).
% 2.44/0.72  fof(f424,plain,(
% 2.44/0.72    spl3_31 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.44/0.72  fof(f432,plain,(
% 2.44/0.72    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl3_31),
% 2.44/0.72    inference(resolution,[],[f426,f91])).
% 2.44/0.72  fof(f91,plain,(
% 2.44/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.44/0.72    inference(cnf_transformation,[],[f25])).
% 2.44/0.72  fof(f25,axiom,(
% 2.44/0.72    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.44/0.72  fof(f426,plain,(
% 2.44/0.72    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_31),
% 2.44/0.72    inference(avatar_component_clause,[],[f424])).
% 2.44/0.72  fof(f437,plain,(
% 2.44/0.72    spl3_32 | ~spl3_3 | ~spl3_12),
% 2.44/0.72    inference(avatar_split_clause,[],[f217,f204,f117,f434])).
% 2.44/0.72  fof(f204,plain,(
% 2.44/0.72    spl3_12 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.44/0.72  fof(f217,plain,(
% 2.44/0.72    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_12)),
% 2.44/0.72    inference(resolution,[],[f206,f121])).
% 2.44/0.72  fof(f121,plain,(
% 2.44/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(sK1,X0) = k4_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl3_3),
% 2.44/0.72    inference(resolution,[],[f119,f98])).
% 2.44/0.72  fof(f206,plain,(
% 2.44/0.72    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_12),
% 2.44/0.72    inference(avatar_component_clause,[],[f204])).
% 2.44/0.72  fof(f427,plain,(
% 2.44/0.72    spl3_31 | ~spl3_29),
% 2.44/0.72    inference(avatar_split_clause,[],[f421,f408,f424])).
% 2.44/0.72  fof(f421,plain,(
% 2.44/0.72    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_29),
% 2.44/0.72    inference(superposition,[],[f72,f410])).
% 2.44/0.72  fof(f72,plain,(
% 2.44/0.72    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.44/0.72    inference(cnf_transformation,[],[f8])).
% 2.44/0.72  fof(f8,axiom,(
% 2.44/0.72    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.44/0.72  fof(f411,plain,(
% 2.44/0.72    spl3_29 | ~spl3_3 | ~spl3_20),
% 2.44/0.72    inference(avatar_split_clause,[],[f303,f277,f117,f408])).
% 2.44/0.72  fof(f280,plain,(
% 2.44/0.72    spl3_20 | ~spl3_2 | ~spl3_3),
% 2.44/0.72    inference(avatar_split_clause,[],[f209,f117,f105,f277])).
% 2.44/0.72  fof(f209,plain,(
% 2.44/0.72    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3)),
% 2.44/0.72    inference(resolution,[],[f113,f119])).
% 2.44/0.72  fof(f113,plain,(
% 2.44/0.72    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X2) = k7_subset_1(u1_struct_0(sK0),X2,k2_tops_1(sK0,X2))) ) | ~spl3_2),
% 2.44/0.72    inference(resolution,[],[f107,f69])).
% 2.44/0.72  fof(f69,plain,(
% 2.44/0.72    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.44/0.72    inference(cnf_transformation,[],[f39])).
% 2.44/0.72  fof(f39,plain,(
% 2.44/0.72    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.44/0.72    inference(ennf_transformation,[],[f31])).
% 2.44/0.72  fof(f31,axiom,(
% 2.44/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.44/0.72  fof(f207,plain,(
% 2.44/0.72    spl3_12 | ~spl3_2 | ~spl3_3),
% 2.44/0.72    inference(avatar_split_clause,[],[f185,f117,f105,f204])).
% 2.44/0.72  fof(f185,plain,(
% 2.44/0.72    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3)),
% 2.44/0.72    inference(resolution,[],[f111,f119])).
% 2.44/0.72  fof(f111,plain,(
% 2.44/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_2),
% 2.44/0.72    inference(resolution,[],[f107,f87])).
% 2.44/0.72  fof(f87,plain,(
% 2.44/0.72    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.44/0.72    inference(cnf_transformation,[],[f51])).
% 2.44/0.72  fof(f51,plain,(
% 2.44/0.72    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.44/0.72    inference(flattening,[],[f50])).
% 2.44/0.72  fof(f50,plain,(
% 2.44/0.72    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.44/0.72    inference(ennf_transformation,[],[f26])).
% 2.44/0.72  fof(f26,axiom,(
% 2.44/0.72    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.44/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.44/0.72  fof(f190,plain,(
% 2.44/0.72    spl3_11 | ~spl3_10),
% 2.44/0.72    inference(avatar_split_clause,[],[f183,f178,f187])).
% 2.44/0.72  fof(f183,plain,(
% 2.44/0.72    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(sK1)) | ~spl3_10),
% 2.44/0.72    inference(resolution,[],[f180,f91])).
% 2.44/0.72  fof(f180,plain,(
% 2.44/0.72    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl3_10),
% 2.44/0.72    inference(avatar_component_clause,[],[f178])).
% 2.44/0.72  fof(f181,plain,(
% 2.44/0.72    spl3_10 | ~spl3_9),
% 2.44/0.72    inference(avatar_split_clause,[],[f175,f158,f178])).
% 2.44/0.72  fof(f158,plain,(
% 2.44/0.72    spl3_9 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.44/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.44/0.72  fof(f175,plain,(
% 2.44/0.72    r1_tarski(k2_tops_1(sK0,sK1),sK1) | ~spl3_9),
% 2.44/0.72    inference(superposition,[],[f72,f160])).
% 2.44/0.72  fof(f160,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl3_9),
% 2.44/0.72    inference(avatar_component_clause,[],[f158])).
% 2.44/0.72  fof(f161,plain,(
% 2.44/0.72    spl3_9 | ~spl3_3 | ~spl3_5),
% 2.44/0.72    inference(avatar_split_clause,[],[f139,f131,f117,f158])).
% 2.44/0.72  fof(f139,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_5)),
% 2.44/0.72    inference(subsumption_resolution,[],[f137,f119])).
% 2.44/0.72  fof(f137,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) = k4_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 2.44/0.72    inference(superposition,[],[f133,f94])).
% 2.44/0.72  fof(f134,plain,(
% 2.44/0.72    spl3_4 | spl3_5),
% 2.44/0.72    inference(avatar_split_clause,[],[f60,f131,f127])).
% 2.44/0.72  fof(f60,plain,(
% 2.44/0.72    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | v4_pre_topc(sK1,sK0)),
% 2.44/0.72    inference(cnf_transformation,[],[f36])).
% 2.44/0.72  fof(f120,plain,(
% 2.44/0.72    spl3_3),
% 2.44/0.72    inference(avatar_split_clause,[],[f62,f117])).
% 2.44/0.72  fof(f62,plain,(
% 2.44/0.72    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.44/0.72    inference(cnf_transformation,[],[f36])).
% 2.44/0.72  fof(f108,plain,(
% 2.44/0.72    spl3_2),
% 2.44/0.72    inference(avatar_split_clause,[],[f64,f105])).
% 2.44/0.72  fof(f64,plain,(
% 2.44/0.72    l1_pre_topc(sK0)),
% 2.44/0.72    inference(cnf_transformation,[],[f36])).
% 2.44/0.72  fof(f103,plain,(
% 2.44/0.72    spl3_1),
% 2.44/0.72    inference(avatar_split_clause,[],[f63,f100])).
% 2.44/0.72  fof(f63,plain,(
% 2.44/0.72    v2_pre_topc(sK0)),
% 2.44/0.72    inference(cnf_transformation,[],[f36])).
% 2.44/0.72  % SZS output end Proof for theBenchmark
% 2.44/0.72  % (9151)------------------------------
% 2.44/0.72  % (9151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.44/0.72  % (9151)Termination reason: Refutation
% 2.44/0.72  
% 2.44/0.72  % (9151)Memory used [KB]: 12537
% 2.44/0.72  % (9151)Time elapsed: 0.303 s
% 2.44/0.72  % (9151)------------------------------
% 2.44/0.72  % (9151)------------------------------
% 2.44/0.72  % (9126)Success in time 0.364 s
%------------------------------------------------------------------------------
