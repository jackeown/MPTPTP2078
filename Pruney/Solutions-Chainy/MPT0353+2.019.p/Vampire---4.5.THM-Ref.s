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
% DateTime   : Thu Dec  3 12:44:23 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 161 expanded)
%              Number of leaves         :   29 (  75 expanded)
%              Depth                    :    7
%              Number of atoms          :  240 ( 397 expanded)
%              Number of equality atoms :   69 ( 117 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f467,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f63,f69,f73,f77,f81,f85,f152,f188,f192,f215,f279,f456,f465])).

fof(f465,plain,
    ( spl3_23
    | ~ spl3_32
    | ~ spl3_39 ),
    inference(avatar_contradiction_clause,[],[f464])).

fof(f464,plain,
    ( $false
    | spl3_23
    | ~ spl3_32
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f183,f461])).

fof(f461,plain,
    ( ! [X2] : k3_xboole_0(sK1,k4_xboole_0(sK0,X2)) = k4_xboole_0(sK1,X2)
    | ~ spl3_32
    | ~ spl3_39 ),
    inference(superposition,[],[f278,f455])).

fof(f455,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f453])).

fof(f453,plain,
    ( spl3_39
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f278,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f277])).

fof(f277,plain,
    ( spl3_32
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f183,plain,
    ( k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl3_23
  <=> k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f456,plain,
    ( spl3_39
    | ~ spl3_17
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f220,f213,f149,f453])).

fof(f149,plain,
    ( spl3_17
  <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f213,plain,
    ( spl3_27
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f220,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_17
    | ~ spl3_27 ),
    inference(superposition,[],[f214,f151])).

fof(f151,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f149])).

fof(f214,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f213])).

fof(f279,plain,
    ( spl3_32
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f106,f75,f53,f277])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f75,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f106,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(superposition,[],[f76,f54])).

fof(f54,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f76,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f215,plain,
    ( spl3_27
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f94,f67,f61,f49,f213])).

fof(f49,plain,
    ( spl3_4
  <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f67,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f94,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1))
    | ~ spl3_4
    | ~ spl3_7
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f92,f62])).

fof(f62,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f92,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))
    | ~ spl3_4
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f50,f68])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f50,plain,
    ( ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f192,plain,
    ( ~ spl3_4
    | spl3_24 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | ~ spl3_4
    | spl3_24 ),
    inference(unit_resulting_resolution,[],[f50,f187])).

fof(f187,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl3_24
  <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f188,plain,
    ( ~ spl3_23
    | ~ spl3_24
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f123,f83,f79,f67,f44,f39,f34,f185,f181])).

fof(f34,plain,
    ( spl3_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f44,plain,
    ( spl3_3
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f83,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f123,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))
    | k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f122,f91])).

fof(f91,plain,
    ( k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f41,f68])).

fof(f41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f122,plain,
    ( k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | ~ spl3_8
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f121,f114])).

fof(f114,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(sK0,sK1,X0)
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f36,f80])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f36,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f121,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | spl3_3
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f120,f91])).

fof(f120,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k3_subset_1(sK0,sK2))
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))
    | spl3_3
    | ~ spl3_12 ),
    inference(superposition,[],[f46,f84])).

fof(f84,plain,
    ( ! [X2,X0,X1] :
        ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f83])).

fof(f46,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f152,plain,
    ( spl3_17
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f104,f71,f67,f34,f149])).

fof(f71,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f104,plain,
    ( sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f95,f90])).

fof(f90,plain,
    ( k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f36,f68])).

fof(f95,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f36,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f85,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f31,f83])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f81,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f30,f79])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f77,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f29,f75])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f73,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f71])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f27,f67])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f61])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f32,f49])).

fof(f32,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f23,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f23,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f47,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f18,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f34])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:40:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.40  % (27514)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.13/0.41  % (27506)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.19/0.44  % (27503)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.44  % (27502)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.45  % (27499)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.45  % (27513)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.45  % (27510)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.46  % (27505)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.46  % (27507)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.46  % (27511)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.47  % (27510)Refutation not found, incomplete strategy% (27510)------------------------------
% 0.19/0.47  % (27510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (27510)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (27510)Memory used [KB]: 10618
% 0.19/0.47  % (27510)Time elapsed: 0.067 s
% 0.19/0.47  % (27510)------------------------------
% 0.19/0.47  % (27510)------------------------------
% 0.19/0.47  % (27512)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.47  % (27501)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.47  % (27500)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.47  % (27504)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.48  % (27515)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.48  % (27508)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.48  % (27509)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.49  % (27516)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.49  % (27504)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f467,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f63,f69,f73,f77,f81,f85,f152,f188,f192,f215,f279,f456,f465])).
% 0.19/0.49  fof(f465,plain,(
% 0.19/0.49    spl3_23 | ~spl3_32 | ~spl3_39),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f464])).
% 0.19/0.49  fof(f464,plain,(
% 0.19/0.49    $false | (spl3_23 | ~spl3_32 | ~spl3_39)),
% 0.19/0.49    inference(subsumption_resolution,[],[f183,f461])).
% 0.19/0.49  fof(f461,plain,(
% 0.19/0.49    ( ! [X2] : (k3_xboole_0(sK1,k4_xboole_0(sK0,X2)) = k4_xboole_0(sK1,X2)) ) | (~spl3_32 | ~spl3_39)),
% 0.19/0.49    inference(superposition,[],[f278,f455])).
% 0.19/0.49  fof(f455,plain,(
% 0.19/0.49    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_39),
% 0.19/0.49    inference(avatar_component_clause,[],[f453])).
% 0.19/0.49  fof(f453,plain,(
% 0.19/0.49    spl3_39 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.19/0.49  fof(f278,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)) ) | ~spl3_32),
% 0.19/0.49    inference(avatar_component_clause,[],[f277])).
% 0.19/0.49  fof(f277,plain,(
% 0.19/0.49    spl3_32 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.19/0.49  fof(f183,plain,(
% 0.19/0.49    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | spl3_23),
% 0.19/0.49    inference(avatar_component_clause,[],[f181])).
% 0.19/0.49  fof(f181,plain,(
% 0.19/0.49    spl3_23 <=> k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) = k4_xboole_0(sK1,sK2)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.19/0.49  fof(f456,plain,(
% 0.19/0.49    spl3_39 | ~spl3_17 | ~spl3_27),
% 0.19/0.49    inference(avatar_split_clause,[],[f220,f213,f149,f453])).
% 0.19/0.49  fof(f149,plain,(
% 0.19/0.49    spl3_17 <=> sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.19/0.49  fof(f213,plain,(
% 0.19/0.49    spl3_27 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.19/0.49  fof(f220,plain,(
% 0.19/0.49    sK1 = k3_xboole_0(sK0,sK1) | (~spl3_17 | ~spl3_27)),
% 0.19/0.49    inference(superposition,[],[f214,f151])).
% 0.19/0.49  fof(f151,plain,(
% 0.19/0.49    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_17),
% 0.19/0.49    inference(avatar_component_clause,[],[f149])).
% 0.19/0.49  fof(f214,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1))) ) | ~spl3_27),
% 0.19/0.49    inference(avatar_component_clause,[],[f213])).
% 0.19/0.49  fof(f279,plain,(
% 0.19/0.49    spl3_32 | ~spl3_5 | ~spl3_10),
% 0.19/0.49    inference(avatar_split_clause,[],[f106,f75,f53,f277])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    spl3_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.49  fof(f75,plain,(
% 0.19/0.49    spl3_10 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.49  fof(f106,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)) ) | (~spl3_5 | ~spl3_10)),
% 0.19/0.49    inference(superposition,[],[f76,f54])).
% 0.19/0.49  fof(f54,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.19/0.49    inference(avatar_component_clause,[],[f53])).
% 0.19/0.49  fof(f76,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl3_10),
% 0.19/0.49    inference(avatar_component_clause,[],[f75])).
% 0.19/0.49  fof(f215,plain,(
% 0.19/0.49    spl3_27 | ~spl3_4 | ~spl3_7 | ~spl3_8),
% 0.19/0.49    inference(avatar_split_clause,[],[f94,f67,f61,f49,f213])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    spl3_4 <=> ! [X1,X0] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.49  fof(f61,plain,(
% 0.19/0.49    spl3_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.49  fof(f67,plain,(
% 0.19/0.49    spl3_8 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.49  fof(f94,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_subset_1(X0,k4_xboole_0(X0,X1))) ) | (~spl3_4 | ~spl3_7 | ~spl3_8)),
% 0.19/0.49    inference(forward_demodulation,[],[f92,f62])).
% 0.19/0.49  fof(f62,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl3_7),
% 0.19/0.49    inference(avatar_component_clause,[],[f61])).
% 0.19/0.49  fof(f92,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_subset_1(X0,k4_xboole_0(X0,X1))) ) | (~spl3_4 | ~spl3_8)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f50,f68])).
% 0.19/0.49  fof(f68,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_8),
% 0.19/0.49    inference(avatar_component_clause,[],[f67])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) ) | ~spl3_4),
% 0.19/0.49    inference(avatar_component_clause,[],[f49])).
% 0.19/0.49  fof(f192,plain,(
% 0.19/0.49    ~spl3_4 | spl3_24),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f189])).
% 0.19/0.49  fof(f189,plain,(
% 0.19/0.49    $false | (~spl3_4 | spl3_24)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f50,f187])).
% 0.19/0.49  fof(f187,plain,(
% 0.19/0.49    ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | spl3_24),
% 0.19/0.49    inference(avatar_component_clause,[],[f185])).
% 0.19/0.49  fof(f185,plain,(
% 0.19/0.49    spl3_24 <=> m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.19/0.49  fof(f188,plain,(
% 0.19/0.49    ~spl3_23 | ~spl3_24 | ~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_8 | ~spl3_11 | ~spl3_12),
% 0.19/0.49    inference(avatar_split_clause,[],[f123,f83,f79,f67,f44,f39,f34,f185,f181])).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    spl3_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.49  fof(f44,plain,(
% 0.19/0.49    spl3_3 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.49  fof(f79,plain,(
% 0.19/0.49    spl3_11 <=> ! [X1,X0,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.49  fof(f83,plain,(
% 0.19/0.49    spl3_12 <=> ! [X1,X0,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.19/0.49  fof(f123,plain,(
% 0.19/0.49    ~m1_subset_1(k4_xboole_0(sK0,sK2),k1_zfmisc_1(sK0)) | k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | (~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_8 | ~spl3_11 | ~spl3_12)),
% 0.19/0.49    inference(forward_demodulation,[],[f122,f91])).
% 0.19/0.49  fof(f91,plain,(
% 0.19/0.49    k3_subset_1(sK0,sK2) = k4_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_8)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f41,f68])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f39])).
% 0.19/0.49  fof(f122,plain,(
% 0.19/0.49    k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) != k4_xboole_0(sK1,sK2) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl3_1 | ~spl3_2 | spl3_3 | ~spl3_8 | ~spl3_11 | ~spl3_12)),
% 0.19/0.49    inference(forward_demodulation,[],[f121,f114])).
% 0.19/0.49  fof(f114,plain,(
% 0.19/0.49    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(sK0,sK1,X0)) ) | (~spl3_1 | ~spl3_11)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f36,f80])).
% 0.19/0.49  fof(f80,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_11),
% 0.19/0.49    inference(avatar_component_clause,[],[f79])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f34])).
% 0.19/0.49  fof(f121,plain,(
% 0.19/0.49    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k4_xboole_0(sK0,sK2)) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | (~spl3_2 | spl3_3 | ~spl3_8 | ~spl3_12)),
% 0.19/0.49    inference(forward_demodulation,[],[f120,f91])).
% 0.19/0.49  fof(f120,plain,(
% 0.19/0.49    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) | (spl3_3 | ~spl3_12)),
% 0.19/0.49    inference(superposition,[],[f46,f84])).
% 0.19/0.49  fof(f84,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) ) | ~spl3_12),
% 0.19/0.49    inference(avatar_component_clause,[],[f83])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) | spl3_3),
% 0.19/0.49    inference(avatar_component_clause,[],[f44])).
% 0.19/0.49  fof(f152,plain,(
% 0.19/0.49    spl3_17 | ~spl3_1 | ~spl3_8 | ~spl3_9),
% 0.19/0.49    inference(avatar_split_clause,[],[f104,f71,f67,f34,f149])).
% 0.19/0.49  fof(f71,plain,(
% 0.19/0.49    spl3_9 <=> ! [X1,X0] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.49  fof(f104,plain,(
% 0.19/0.49    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | (~spl3_1 | ~spl3_8 | ~spl3_9)),
% 0.19/0.49    inference(forward_demodulation,[],[f95,f90])).
% 0.19/0.49  fof(f90,plain,(
% 0.19/0.49    k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1) | (~spl3_1 | ~spl3_8)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f36,f68])).
% 0.19/0.49  fof(f95,plain,(
% 0.19/0.49    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | (~spl3_1 | ~spl3_9)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f36,f72])).
% 0.19/0.49  fof(f72,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) ) | ~spl3_9),
% 0.19/0.49    inference(avatar_component_clause,[],[f71])).
% 0.19/0.49  fof(f85,plain,(
% 0.19/0.49    spl3_12),
% 0.19/0.49    inference(avatar_split_clause,[],[f31,f83])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.19/0.49  fof(f81,plain,(
% 0.19/0.49    spl3_11),
% 0.19/0.49    inference(avatar_split_clause,[],[f30,f79])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.19/0.49  fof(f77,plain,(
% 0.19/0.49    spl3_10),
% 0.19/0.49    inference(avatar_split_clause,[],[f29,f75])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.19/0.49  fof(f73,plain,(
% 0.19/0.49    spl3_9),
% 0.19/0.49    inference(avatar_split_clause,[],[f28,f71])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f14])).
% 0.19/0.49  fof(f14,plain,(
% 0.19/0.49    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.19/0.49  fof(f69,plain,(
% 0.19/0.49    spl3_8),
% 0.19/0.49    inference(avatar_split_clause,[],[f27,f67])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f13])).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.49  fof(f63,plain,(
% 0.19/0.49    spl3_7),
% 0.19/0.49    inference(avatar_split_clause,[],[f26,f61])).
% 0.19/0.49  fof(f26,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.49  fof(f55,plain,(
% 0.19/0.49    spl3_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f24,f53])).
% 0.19/0.49  fof(f24,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    spl3_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f32,f49])).
% 0.19/0.49  fof(f32,plain,(
% 0.19/0.49    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(forward_demodulation,[],[f23,f25])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,axiom,(
% 0.19/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.19/0.49    inference(cnf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    ~spl3_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f22,f44])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 0.19/0.49    inference(cnf_transformation,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f18,f17])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f11])).
% 0.19/0.49  fof(f11,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.19/0.49    inference(negated_conjecture,[],[f10])).
% 0.19/0.49  fof(f10,conjecture,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 0.19/0.49  fof(f42,plain,(
% 0.19/0.49    spl3_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f21,f39])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.19/0.49    inference(cnf_transformation,[],[f19])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    spl3_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f20,f34])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.49    inference(cnf_transformation,[],[f19])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (27504)------------------------------
% 0.19/0.49  % (27504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (27504)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (27504)Memory used [KB]: 6524
% 0.19/0.49  % (27504)Time elapsed: 0.073 s
% 0.19/0.49  % (27504)------------------------------
% 0.19/0.49  % (27504)------------------------------
% 0.19/0.49  % (27498)Success in time 0.145 s
%------------------------------------------------------------------------------
