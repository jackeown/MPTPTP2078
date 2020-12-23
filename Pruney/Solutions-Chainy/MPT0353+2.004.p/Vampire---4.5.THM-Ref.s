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
% DateTime   : Thu Dec  3 12:44:20 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 299 expanded)
%              Number of leaves         :   28 ( 117 expanded)
%              Depth                    :   11
%              Number of atoms          :  257 ( 613 expanded)
%              Number of equality atoms :   93 ( 208 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4073,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f50,f55,f70,f71,f140,f141,f1712,f1720,f1754,f1807,f1809,f2008,f2016,f4035])).

fof(f4035,plain,
    ( spl3_35
    | ~ spl3_3
    | ~ spl3_29
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f4034,f2013,f1717,f52,f1794])).

fof(f1794,plain,
    ( spl3_35
  <=> k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f52,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f1717,plain,
    ( spl3_29
  <=> sK2 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f2013,plain,
    ( spl3_41
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f4034,plain,
    ( k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | ~ spl3_3
    | ~ spl3_29
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f4033,f2015])).

fof(f2015,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f2013])).

fof(f4033,plain,
    ( k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) = k7_subset_1(sK0,k3_xboole_0(sK0,sK1),sK2)
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f3993,f97])).

fof(f97,plain,(
    ! [X4,X2,X3] : k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X2)) ),
    inference(superposition,[],[f34,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f3993,plain,
    ( k7_subset_1(sK0,k3_xboole_0(sK0,sK1),sK2) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2))
    | ~ spl3_3
    | ~ spl3_29 ),
    inference(superposition,[],[f193,f1839])).

fof(f1839,plain,
    ( ! [X1] : k3_xboole_0(X1,sK2) = k3_xboole_0(sK0,k3_xboole_0(X1,sK2))
    | ~ spl3_29 ),
    inference(superposition,[],[f1730,f29])).

fof(f1730,plain,
    ( ! [X4] : k3_xboole_0(sK2,X4) = k3_xboole_0(sK0,k3_xboole_0(sK2,X4))
    | ~ spl3_29 ),
    inference(superposition,[],[f33,f1719])).

fof(f1719,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f1717])).

fof(f33,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f193,plain,
    ( ! [X0,X1] : k7_subset_1(sK0,k3_xboole_0(X0,sK1),X1) = k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(X0,k3_xboole_0(sK1,X1)))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f178,f33])).

fof(f178,plain,
    ( ! [X0,X1] : k7_subset_1(sK0,k3_xboole_0(X0,sK1),X1) = k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k3_xboole_0(X0,sK1),X1))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f172,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f37,f30])).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f172,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f85,f88])).

fof(f88,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK1) = k3_xboole_0(X0,sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f54,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f54,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f85,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(sK0,X0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f54,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f2016,plain,
    ( spl3_41
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f2011,f2005,f61,f52,f2013])).

fof(f61,plain,
    ( spl3_4
  <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f2005,plain,
    ( spl3_40
  <=> k3_subset_1(sK0,sK1) = k3_subset_1(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f2011,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_40 ),
    inference(forward_demodulation,[],[f2010,f63])).

fof(f63,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f61])).

fof(f2010,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k3_xboole_0(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_40 ),
    inference(superposition,[],[f183,f2007])).

fof(f2007,plain,
    ( k3_subset_1(sK0,sK1) = k3_subset_1(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f2005])).

fof(f183,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,k3_xboole_0(X0,sK1)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f172,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2008,plain,
    ( spl3_40
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f2003,f131,f52,f2005])).

fof(f131,plain,
    ( spl3_6
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f2003,plain,
    ( k3_subset_1(sK0,sK1) = k3_subset_1(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f1995,f133])).

fof(f133,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f131])).

fof(f1995,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(superposition,[],[f179,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f33,f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f179,plain,
    ( ! [X0] : k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,sK1))) = k3_subset_1(sK0,k3_xboole_0(X0,sK1))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f172,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1809,plain,
    ( ~ spl3_35
    | ~ spl3_3
    | spl3_37 ),
    inference(avatar_split_clause,[],[f1808,f1804,f52,f1794])).

fof(f1804,plain,
    ( spl3_37
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f1808,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)
    | ~ spl3_3
    | spl3_37 ),
    inference(superposition,[],[f1806,f215])).

fof(f215,plain,
    ( ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(sK0,sK1,X0)
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f108,f88])).

fof(f108,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK1) = k9_subset_1(sK0,sK1,X0)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f54,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f1806,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))
    | spl3_37 ),
    inference(avatar_component_clause,[],[f1804])).

fof(f1807,plain,
    ( ~ spl3_37
    | spl3_1
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f1787,f1749,f42,f1804])).

fof(f42,plain,
    ( spl3_1
  <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1749,plain,
    ( spl3_30
  <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f1787,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))
    | spl3_1
    | ~ spl3_30 ),
    inference(backward_demodulation,[],[f44,f1751])).

fof(f1751,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f1749])).

fof(f44,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f1754,plain,
    ( spl3_30
    | ~ spl3_2
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f1753,f1717,f47,f1749])).

fof(f47,plain,
    ( spl3_2
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1753,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f1724,f1719])).

fof(f1724,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_29 ),
    inference(superposition,[],[f156,f1719])).

fof(f156,plain,
    ( ! [X0] : k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,sK2))) = k3_subset_1(sK0,k3_xboole_0(X0,sK2))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f142,f39])).

fof(f142,plain,
    ( ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f84,f87])).

fof(f87,plain,
    ( ! [X0] : k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f49,f36])).

fof(f49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f84,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(sK0,X0,sK2),k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f49,f35])).

fof(f1720,plain,
    ( spl3_29
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f1715,f1709,f66,f47,f1717])).

fof(f66,plain,
    ( spl3_5
  <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1709,plain,
    ( spl3_28
  <=> k3_subset_1(sK0,sK2) = k3_subset_1(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1715,plain,
    ( sK2 = k3_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_5
    | ~ spl3_28 ),
    inference(forward_demodulation,[],[f1714,f68])).

fof(f68,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f1714,plain,
    ( k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k3_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_28 ),
    inference(superposition,[],[f160,f1711])).

fof(f1711,plain,
    ( k3_subset_1(sK0,sK2) = k3_subset_1(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f1709])).

fof(f160,plain,
    ( ! [X0] : k3_xboole_0(X0,sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k3_xboole_0(X0,sK2)))
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f142,f32])).

fof(f1712,plain,
    ( spl3_28
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f1707,f136,f47,f1709])).

fof(f136,plain,
    ( spl3_7
  <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1707,plain,
    ( k3_subset_1(sK0,sK2) = k3_subset_1(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f1705,f138])).

fof(f138,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f136])).

fof(f1705,plain,
    ( k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(superposition,[],[f156,f72])).

fof(f141,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f126,f52,f131])).

fof(f126,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f39,f54])).

fof(f140,plain,
    ( spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f125,f47,f136])).

fof(f125,plain,
    ( k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f39,f49])).

fof(f71,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f59,f52,f61])).

fof(f59,plain,
    ( sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f32,f54])).

fof(f70,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f58,f47,f66])).

fof(f58,plain,
    ( sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))
    | ~ spl3_2 ),
    inference(resolution,[],[f32,f49])).

fof(f55,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f25,f52])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22])).

fof(f22,plain,
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

fof(f23,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f50,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f47])).

fof(f26,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f45,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f27,f42])).

fof(f27,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (12207)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.45  % (12202)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (12203)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (12192)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (12190)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (12195)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (12200)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (12204)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (12194)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (12193)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (12199)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (12196)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (12191)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.50  % (12201)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (12198)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.50  % (12205)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (12206)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (12197)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 2.20/0.63  % (12196)Refutation found. Thanks to Tanya!
% 2.20/0.63  % SZS status Theorem for theBenchmark
% 2.20/0.63  % SZS output start Proof for theBenchmark
% 2.20/0.63  fof(f4073,plain,(
% 2.20/0.63    $false),
% 2.20/0.63    inference(avatar_sat_refutation,[],[f45,f50,f55,f70,f71,f140,f141,f1712,f1720,f1754,f1807,f1809,f2008,f2016,f4035])).
% 2.20/0.63  fof(f4035,plain,(
% 2.20/0.63    spl3_35 | ~spl3_3 | ~spl3_29 | ~spl3_41),
% 2.20/0.63    inference(avatar_split_clause,[],[f4034,f2013,f1717,f52,f1794])).
% 2.20/0.63  fof(f1794,plain,(
% 2.20/0.63    spl3_35 <=> k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(k5_xboole_0(sK0,sK2),sK1)),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 2.20/0.63  fof(f52,plain,(
% 2.20/0.63    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.20/0.63  fof(f1717,plain,(
% 2.20/0.63    spl3_29 <=> sK2 = k3_xboole_0(sK0,sK2)),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 2.20/0.63  fof(f2013,plain,(
% 2.20/0.63    spl3_41 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 2.20/0.63  fof(f4034,plain,(
% 2.20/0.63    k7_subset_1(sK0,sK1,sK2) = k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) | (~spl3_3 | ~spl3_29 | ~spl3_41)),
% 2.20/0.63    inference(forward_demodulation,[],[f4033,f2015])).
% 2.20/0.63  fof(f2015,plain,(
% 2.20/0.63    sK1 = k3_xboole_0(sK0,sK1) | ~spl3_41),
% 2.20/0.63    inference(avatar_component_clause,[],[f2013])).
% 2.20/0.63  fof(f4033,plain,(
% 2.20/0.63    k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) = k7_subset_1(sK0,k3_xboole_0(sK0,sK1),sK2) | (~spl3_3 | ~spl3_29)),
% 2.20/0.63    inference(forward_demodulation,[],[f3993,f97])).
% 2.20/0.63  fof(f97,plain,(
% 2.20/0.63    ( ! [X4,X2,X3] : (k3_xboole_0(k5_xboole_0(X4,X2),X3) = k5_xboole_0(k3_xboole_0(X4,X3),k3_xboole_0(X3,X2))) )),
% 2.20/0.63    inference(superposition,[],[f34,f29])).
% 2.20/0.63  fof(f29,plain,(
% 2.20/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.20/0.63    inference(cnf_transformation,[],[f1])).
% 2.20/0.63  fof(f1,axiom,(
% 2.20/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.20/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.20/0.63  fof(f34,plain,(
% 2.20/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.20/0.63    inference(cnf_transformation,[],[f4])).
% 2.20/0.63  fof(f4,axiom,(
% 2.20/0.63    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.20/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.20/0.63  fof(f3993,plain,(
% 2.20/0.63    k7_subset_1(sK0,k3_xboole_0(sK0,sK1),sK2) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,sK2)) | (~spl3_3 | ~spl3_29)),
% 2.20/0.63    inference(superposition,[],[f193,f1839])).
% 2.20/0.63  fof(f1839,plain,(
% 2.20/0.63    ( ! [X1] : (k3_xboole_0(X1,sK2) = k3_xboole_0(sK0,k3_xboole_0(X1,sK2))) ) | ~spl3_29),
% 2.20/0.63    inference(superposition,[],[f1730,f29])).
% 2.20/0.63  fof(f1730,plain,(
% 2.20/0.63    ( ! [X4] : (k3_xboole_0(sK2,X4) = k3_xboole_0(sK0,k3_xboole_0(sK2,X4))) ) | ~spl3_29),
% 2.20/0.63    inference(superposition,[],[f33,f1719])).
% 2.20/0.63  fof(f1719,plain,(
% 2.20/0.63    sK2 = k3_xboole_0(sK0,sK2) | ~spl3_29),
% 2.20/0.63    inference(avatar_component_clause,[],[f1717])).
% 2.20/0.63  fof(f33,plain,(
% 2.20/0.63    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 2.20/0.63    inference(cnf_transformation,[],[f5])).
% 2.20/0.63  fof(f5,axiom,(
% 2.20/0.63    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.20/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 2.20/0.63  fof(f193,plain,(
% 2.20/0.63    ( ! [X0,X1] : (k7_subset_1(sK0,k3_xboole_0(X0,sK1),X1) = k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(X0,k3_xboole_0(sK1,X1)))) ) | ~spl3_3),
% 2.20/0.63    inference(forward_demodulation,[],[f178,f33])).
% 2.20/0.63  fof(f178,plain,(
% 2.20/0.63    ( ! [X0,X1] : (k7_subset_1(sK0,k3_xboole_0(X0,sK1),X1) = k5_xboole_0(k3_xboole_0(X0,sK1),k3_xboole_0(k3_xboole_0(X0,sK1),X1))) ) | ~spl3_3),
% 2.20/0.63    inference(unit_resulting_resolution,[],[f172,f40])).
% 2.20/0.63  fof(f40,plain,(
% 2.20/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))) )),
% 2.20/0.63    inference(definition_unfolding,[],[f37,f30])).
% 2.20/0.63  fof(f30,plain,(
% 2.20/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.20/0.63    inference(cnf_transformation,[],[f3])).
% 2.20/0.63  fof(f3,axiom,(
% 2.20/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.20/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.20/0.63  fof(f37,plain,(
% 2.20/0.63    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.20/0.63    inference(cnf_transformation,[],[f20])).
% 2.20/0.63  fof(f20,plain,(
% 2.20/0.63    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.63    inference(ennf_transformation,[],[f10])).
% 2.20/0.63  fof(f10,axiom,(
% 2.20/0.63    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.20/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.20/0.63  fof(f172,plain,(
% 2.20/0.63    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(sK0))) ) | ~spl3_3),
% 2.20/0.63    inference(backward_demodulation,[],[f85,f88])).
% 2.20/0.63  fof(f88,plain,(
% 2.20/0.63    ( ! [X0] : (k9_subset_1(sK0,X0,sK1) = k3_xboole_0(X0,sK1)) ) | ~spl3_3),
% 2.20/0.63    inference(unit_resulting_resolution,[],[f54,f36])).
% 2.20/0.63  fof(f36,plain,(
% 2.20/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)) )),
% 2.20/0.63    inference(cnf_transformation,[],[f19])).
% 2.20/0.63  fof(f19,plain,(
% 2.20/0.63    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.20/0.63    inference(ennf_transformation,[],[f11])).
% 2.20/0.63  fof(f11,axiom,(
% 2.20/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 2.20/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.20/0.63  fof(f54,plain,(
% 2.20/0.63    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_3),
% 2.20/0.63    inference(avatar_component_clause,[],[f52])).
% 2.20/0.63  fof(f85,plain,(
% 2.20/0.63    ( ! [X0] : (m1_subset_1(k9_subset_1(sK0,X0,sK1),k1_zfmisc_1(sK0))) ) | ~spl3_3),
% 2.20/0.63    inference(unit_resulting_resolution,[],[f54,f35])).
% 2.20/0.63  fof(f35,plain,(
% 2.20/0.63    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.20/0.63    inference(cnf_transformation,[],[f18])).
% 2.20/0.63  fof(f18,plain,(
% 2.20/0.63    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.20/0.63    inference(ennf_transformation,[],[f8])).
% 2.20/0.63  fof(f8,axiom,(
% 2.20/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.20/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 2.20/0.63  fof(f2016,plain,(
% 2.20/0.63    spl3_41 | ~spl3_3 | ~spl3_4 | ~spl3_40),
% 2.20/0.63    inference(avatar_split_clause,[],[f2011,f2005,f61,f52,f2013])).
% 2.20/0.63  fof(f61,plain,(
% 2.20/0.63    spl3_4 <=> sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.20/0.63  fof(f2005,plain,(
% 2.20/0.63    spl3_40 <=> k3_subset_1(sK0,sK1) = k3_subset_1(sK0,k3_xboole_0(sK0,sK1))),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 2.20/0.63  fof(f2011,plain,(
% 2.20/0.63    sK1 = k3_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_40)),
% 2.20/0.63    inference(forward_demodulation,[],[f2010,f63])).
% 2.20/0.63  fof(f63,plain,(
% 2.20/0.63    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_4),
% 2.20/0.63    inference(avatar_component_clause,[],[f61])).
% 2.20/0.63  fof(f2010,plain,(
% 2.20/0.63    k3_subset_1(sK0,k3_subset_1(sK0,sK1)) = k3_xboole_0(sK0,sK1) | (~spl3_3 | ~spl3_40)),
% 2.20/0.63    inference(superposition,[],[f183,f2007])).
% 2.20/0.63  fof(f2007,plain,(
% 2.20/0.63    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_40),
% 2.20/0.63    inference(avatar_component_clause,[],[f2005])).
% 2.20/0.63  fof(f183,plain,(
% 2.20/0.63    ( ! [X0] : (k3_xboole_0(X0,sK1) = k3_subset_1(sK0,k3_subset_1(sK0,k3_xboole_0(X0,sK1)))) ) | ~spl3_3),
% 2.20/0.63    inference(unit_resulting_resolution,[],[f172,f32])).
% 2.20/0.63  fof(f32,plain,(
% 2.20/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.20/0.63    inference(cnf_transformation,[],[f17])).
% 2.20/0.63  fof(f17,plain,(
% 2.20/0.63    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.63    inference(ennf_transformation,[],[f9])).
% 2.20/0.63  fof(f9,axiom,(
% 2.20/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.20/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.20/0.63  fof(f2008,plain,(
% 2.20/0.63    spl3_40 | ~spl3_3 | ~spl3_6),
% 2.20/0.63    inference(avatar_split_clause,[],[f2003,f131,f52,f2005])).
% 2.20/0.63  fof(f131,plain,(
% 2.20/0.63    spl3_6 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.20/0.63  fof(f2003,plain,(
% 2.20/0.63    k3_subset_1(sK0,sK1) = k3_subset_1(sK0,k3_xboole_0(sK0,sK1)) | (~spl3_3 | ~spl3_6)),
% 2.20/0.63    inference(forward_demodulation,[],[f1995,f133])).
% 2.20/0.63  fof(f133,plain,(
% 2.20/0.63    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_6),
% 2.20/0.63    inference(avatar_component_clause,[],[f131])).
% 2.20/0.63  fof(f1995,plain,(
% 2.20/0.63    k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_3),
% 2.20/0.63    inference(superposition,[],[f179,f72])).
% 2.20/0.63  fof(f72,plain,(
% 2.20/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.20/0.63    inference(superposition,[],[f33,f28])).
% 2.20/0.63  fof(f28,plain,(
% 2.20/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.20/0.63    inference(cnf_transformation,[],[f14])).
% 2.20/0.63  fof(f14,plain,(
% 2.20/0.63    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.20/0.63    inference(rectify,[],[f2])).
% 2.20/0.63  fof(f2,axiom,(
% 2.20/0.63    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.20/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.20/0.63  fof(f179,plain,(
% 2.20/0.63    ( ! [X0] : (k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,sK1))) = k3_subset_1(sK0,k3_xboole_0(X0,sK1))) ) | ~spl3_3),
% 2.20/0.63    inference(unit_resulting_resolution,[],[f172,f39])).
% 2.20/0.63  fof(f39,plain,(
% 2.20/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 2.20/0.63    inference(definition_unfolding,[],[f31,f30])).
% 2.20/0.63  fof(f31,plain,(
% 2.20/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.20/0.63    inference(cnf_transformation,[],[f16])).
% 2.20/0.63  fof(f16,plain,(
% 2.20/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.63    inference(ennf_transformation,[],[f7])).
% 2.20/0.63  fof(f7,axiom,(
% 2.20/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.20/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.20/0.63  fof(f1809,plain,(
% 2.20/0.63    ~spl3_35 | ~spl3_3 | spl3_37),
% 2.20/0.63    inference(avatar_split_clause,[],[f1808,f1804,f52,f1794])).
% 2.20/0.63  fof(f1804,plain,(
% 2.20/0.63    spl3_37 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2))),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 2.20/0.63  fof(f1808,plain,(
% 2.20/0.63    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(k5_xboole_0(sK0,sK2),sK1) | (~spl3_3 | spl3_37)),
% 2.20/0.63    inference(superposition,[],[f1806,f215])).
% 2.20/0.63  fof(f215,plain,(
% 2.20/0.63    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(sK0,sK1,X0)) ) | ~spl3_3),
% 2.20/0.63    inference(forward_demodulation,[],[f108,f88])).
% 2.20/0.63  fof(f108,plain,(
% 2.20/0.63    ( ! [X0] : (k9_subset_1(sK0,X0,sK1) = k9_subset_1(sK0,sK1,X0)) ) | ~spl3_3),
% 2.20/0.63    inference(unit_resulting_resolution,[],[f54,f38])).
% 2.20/0.63  fof(f38,plain,(
% 2.20/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 2.20/0.63    inference(cnf_transformation,[],[f21])).
% 2.20/0.63  fof(f21,plain,(
% 2.20/0.63    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.20/0.63    inference(ennf_transformation,[],[f6])).
% 2.20/0.63  fof(f6,axiom,(
% 2.20/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 2.20/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 2.20/0.63  fof(f1806,plain,(
% 2.20/0.63    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) | spl3_37),
% 2.20/0.63    inference(avatar_component_clause,[],[f1804])).
% 2.20/0.63  fof(f1807,plain,(
% 2.20/0.63    ~spl3_37 | spl3_1 | ~spl3_30),
% 2.20/0.63    inference(avatar_split_clause,[],[f1787,f1749,f42,f1804])).
% 2.20/0.63  fof(f42,plain,(
% 2.20/0.63    spl3_1 <=> k7_subset_1(sK0,sK1,sK2) = k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.20/0.63  fof(f1749,plain,(
% 2.20/0.63    spl3_30 <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 2.20/0.63  fof(f1787,plain,(
% 2.20/0.63    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k5_xboole_0(sK0,sK2)) | (spl3_1 | ~spl3_30)),
% 2.20/0.63    inference(backward_demodulation,[],[f44,f1751])).
% 2.20/0.63  fof(f1751,plain,(
% 2.20/0.63    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | ~spl3_30),
% 2.20/0.63    inference(avatar_component_clause,[],[f1749])).
% 2.20/0.63  fof(f44,plain,(
% 2.20/0.63    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) | spl3_1),
% 2.20/0.63    inference(avatar_component_clause,[],[f42])).
% 2.20/0.63  fof(f1754,plain,(
% 2.20/0.63    spl3_30 | ~spl3_2 | ~spl3_29),
% 2.20/0.63    inference(avatar_split_clause,[],[f1753,f1717,f47,f1749])).
% 2.20/0.63  fof(f47,plain,(
% 2.20/0.63    spl3_2 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.20/0.63  fof(f1753,plain,(
% 2.20/0.63    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_29)),
% 2.20/0.63    inference(forward_demodulation,[],[f1724,f1719])).
% 2.20/0.63  fof(f1724,plain,(
% 2.20/0.63    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | (~spl3_2 | ~spl3_29)),
% 2.20/0.63    inference(superposition,[],[f156,f1719])).
% 2.20/0.63  fof(f156,plain,(
% 2.20/0.63    ( ! [X0] : (k5_xboole_0(sK0,k3_xboole_0(sK0,k3_xboole_0(X0,sK2))) = k3_subset_1(sK0,k3_xboole_0(X0,sK2))) ) | ~spl3_2),
% 2.20/0.63    inference(unit_resulting_resolution,[],[f142,f39])).
% 2.20/0.63  fof(f142,plain,(
% 2.20/0.63    ( ! [X0] : (m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(sK0))) ) | ~spl3_2),
% 2.20/0.63    inference(backward_demodulation,[],[f84,f87])).
% 2.20/0.63  fof(f87,plain,(
% 2.20/0.63    ( ! [X0] : (k9_subset_1(sK0,X0,sK2) = k3_xboole_0(X0,sK2)) ) | ~spl3_2),
% 2.20/0.63    inference(unit_resulting_resolution,[],[f49,f36])).
% 2.20/0.63  fof(f49,plain,(
% 2.20/0.63    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl3_2),
% 2.20/0.63    inference(avatar_component_clause,[],[f47])).
% 2.20/0.63  fof(f84,plain,(
% 2.20/0.63    ( ! [X0] : (m1_subset_1(k9_subset_1(sK0,X0,sK2),k1_zfmisc_1(sK0))) ) | ~spl3_2),
% 2.20/0.63    inference(unit_resulting_resolution,[],[f49,f35])).
% 2.20/0.63  fof(f1720,plain,(
% 2.20/0.63    spl3_29 | ~spl3_2 | ~spl3_5 | ~spl3_28),
% 2.20/0.63    inference(avatar_split_clause,[],[f1715,f1709,f66,f47,f1717])).
% 2.20/0.63  fof(f66,plain,(
% 2.20/0.63    spl3_5 <=> sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.20/0.63  fof(f1709,plain,(
% 2.20/0.63    spl3_28 <=> k3_subset_1(sK0,sK2) = k3_subset_1(sK0,k3_xboole_0(sK0,sK2))),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 2.20/0.63  fof(f1715,plain,(
% 2.20/0.63    sK2 = k3_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_5 | ~spl3_28)),
% 2.20/0.63    inference(forward_demodulation,[],[f1714,f68])).
% 2.20/0.63  fof(f68,plain,(
% 2.20/0.63    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | ~spl3_5),
% 2.20/0.63    inference(avatar_component_clause,[],[f66])).
% 2.20/0.63  fof(f1714,plain,(
% 2.20/0.63    k3_subset_1(sK0,k3_subset_1(sK0,sK2)) = k3_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_28)),
% 2.20/0.63    inference(superposition,[],[f160,f1711])).
% 2.20/0.63  fof(f1711,plain,(
% 2.20/0.63    k3_subset_1(sK0,sK2) = k3_subset_1(sK0,k3_xboole_0(sK0,sK2)) | ~spl3_28),
% 2.20/0.63    inference(avatar_component_clause,[],[f1709])).
% 2.20/0.63  fof(f160,plain,(
% 2.20/0.63    ( ! [X0] : (k3_xboole_0(X0,sK2) = k3_subset_1(sK0,k3_subset_1(sK0,k3_xboole_0(X0,sK2)))) ) | ~spl3_2),
% 2.20/0.63    inference(unit_resulting_resolution,[],[f142,f32])).
% 2.20/0.63  fof(f1712,plain,(
% 2.20/0.63    spl3_28 | ~spl3_2 | ~spl3_7),
% 2.20/0.63    inference(avatar_split_clause,[],[f1707,f136,f47,f1709])).
% 2.20/0.63  fof(f136,plain,(
% 2.20/0.63    spl3_7 <=> k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 2.20/0.63    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.20/0.63  fof(f1707,plain,(
% 2.20/0.63    k3_subset_1(sK0,sK2) = k3_subset_1(sK0,k3_xboole_0(sK0,sK2)) | (~spl3_2 | ~spl3_7)),
% 2.20/0.63    inference(forward_demodulation,[],[f1705,f138])).
% 2.20/0.63  fof(f138,plain,(
% 2.20/0.63    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl3_7),
% 2.20/0.63    inference(avatar_component_clause,[],[f136])).
% 2.20/0.63  fof(f1705,plain,(
% 2.20/0.63    k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) = k3_subset_1(sK0,k3_xboole_0(sK0,sK2)) | ~spl3_2),
% 2.20/0.63    inference(superposition,[],[f156,f72])).
% 2.20/0.63  fof(f141,plain,(
% 2.20/0.63    spl3_6 | ~spl3_3),
% 2.20/0.63    inference(avatar_split_clause,[],[f126,f52,f131])).
% 2.20/0.63  fof(f126,plain,(
% 2.20/0.63    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl3_3),
% 2.20/0.63    inference(resolution,[],[f39,f54])).
% 2.20/0.63  fof(f140,plain,(
% 2.20/0.63    spl3_7 | ~spl3_2),
% 2.20/0.63    inference(avatar_split_clause,[],[f125,f47,f136])).
% 2.20/0.63  fof(f125,plain,(
% 2.20/0.63    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) | ~spl3_2),
% 2.20/0.63    inference(resolution,[],[f39,f49])).
% 2.20/0.63  fof(f71,plain,(
% 2.20/0.63    spl3_4 | ~spl3_3),
% 2.20/0.63    inference(avatar_split_clause,[],[f59,f52,f61])).
% 2.20/0.63  fof(f59,plain,(
% 2.20/0.63    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) | ~spl3_3),
% 2.20/0.63    inference(resolution,[],[f32,f54])).
% 2.20/0.63  fof(f70,plain,(
% 2.20/0.63    spl3_5 | ~spl3_2),
% 2.20/0.63    inference(avatar_split_clause,[],[f58,f47,f66])).
% 2.20/0.63  fof(f58,plain,(
% 2.20/0.63    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) | ~spl3_2),
% 2.20/0.63    inference(resolution,[],[f32,f49])).
% 2.20/0.63  fof(f55,plain,(
% 2.20/0.63    spl3_3),
% 2.20/0.63    inference(avatar_split_clause,[],[f25,f52])).
% 2.20/0.63  fof(f25,plain,(
% 2.20/0.63    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.20/0.63    inference(cnf_transformation,[],[f24])).
% 2.20/0.63  fof(f24,plain,(
% 2.20/0.63    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 2.20/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f23,f22])).
% 2.20/0.63  fof(f22,plain,(
% 2.20/0.63    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 2.20/0.63    introduced(choice_axiom,[])).
% 2.20/0.63  fof(f23,plain,(
% 2.20/0.63    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 2.20/0.63    introduced(choice_axiom,[])).
% 2.20/0.63  fof(f15,plain,(
% 2.20/0.63    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.20/0.63    inference(ennf_transformation,[],[f13])).
% 2.20/0.63  fof(f13,negated_conjecture,(
% 2.20/0.63    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.20/0.63    inference(negated_conjecture,[],[f12])).
% 2.20/0.63  fof(f12,conjecture,(
% 2.20/0.63    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.20/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 2.20/0.63  fof(f50,plain,(
% 2.20/0.63    spl3_2),
% 2.20/0.63    inference(avatar_split_clause,[],[f26,f47])).
% 2.20/0.63  fof(f26,plain,(
% 2.20/0.63    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.20/0.63    inference(cnf_transformation,[],[f24])).
% 2.20/0.63  fof(f45,plain,(
% 2.20/0.63    ~spl3_1),
% 2.20/0.63    inference(avatar_split_clause,[],[f27,f42])).
% 2.20/0.63  fof(f27,plain,(
% 2.20/0.63    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 2.20/0.63    inference(cnf_transformation,[],[f24])).
% 2.20/0.63  % SZS output end Proof for theBenchmark
% 2.20/0.63  % (12196)------------------------------
% 2.20/0.63  % (12196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.63  % (12196)Termination reason: Refutation
% 2.20/0.63  
% 2.20/0.63  % (12196)Memory used [KB]: 9083
% 2.20/0.63  % (12196)Time elapsed: 0.181 s
% 2.20/0.63  % (12196)------------------------------
% 2.20/0.63  % (12196)------------------------------
% 2.20/0.64  % (12189)Success in time 0.284 s
%------------------------------------------------------------------------------
