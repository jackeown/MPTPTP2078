%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:39 EST 2020

% Result     : Theorem 2.58s
% Output     : Refutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 379 expanded)
%              Number of leaves         :   50 ( 164 expanded)
%              Depth                    :   10
%              Number of atoms          :  544 ( 935 expanded)
%              Number of equality atoms :   94 ( 162 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f109,f113,f145,f152,f155,f167,f171,f312,f316,f337,f369,f443,f532,f564,f582,f690,f702,f745,f833,f864,f947,f1063,f1357,f1362,f1857,f1879,f1904,f2009,f2127,f2128])).

fof(f2128,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2127,plain,
    ( spl3_78
    | ~ spl3_69
    | ~ spl3_125
    | ~ spl3_148
    | ~ spl3_156 ),
    inference(avatar_split_clause,[],[f2093,f2007,f1877,f1360,f831,f945])).

fof(f945,plain,
    ( spl3_78
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f831,plain,
    ( spl3_69
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f1360,plain,
    ( spl3_125
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).

fof(f1877,plain,
    ( spl3_148
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_148])])).

fof(f2007,plain,
    ( spl3_156
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_156])])).

fof(f2093,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_69
    | ~ spl3_125
    | ~ spl3_148
    | ~ spl3_156 ),
    inference(forward_demodulation,[],[f2092,f1895])).

fof(f1895,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_69
    | ~ spl3_148 ),
    inference(forward_demodulation,[],[f1890,f1892])).

fof(f1892,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_69
    | ~ spl3_148 ),
    inference(forward_demodulation,[],[f1887,f832])).

fof(f832,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f831])).

fof(f1887,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_148 ),
    inference(resolution,[],[f1878,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1878,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_148 ),
    inference(avatar_component_clause,[],[f1877])).

fof(f1890,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1))
    | ~ spl3_148 ),
    inference(resolution,[],[f1878,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2092,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_125
    | ~ spl3_156 ),
    inference(forward_demodulation,[],[f2087,f2089])).

fof(f2089,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_125
    | ~ spl3_156 ),
    inference(forward_demodulation,[],[f2084,f1361])).

fof(f1361,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_125 ),
    inference(avatar_component_clause,[],[f1360])).

fof(f2084,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_156 ),
    inference(resolution,[],[f2008,f83])).

fof(f2008,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_156 ),
    inference(avatar_component_clause,[],[f2007])).

fof(f2087,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl3_156 ),
    inference(resolution,[],[f2008,f89])).

fof(f2009,plain,
    ( spl3_156
    | ~ spl3_151 ),
    inference(avatar_split_clause,[],[f1923,f1902,f2007])).

fof(f1902,plain,
    ( spl3_151
  <=> r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_151])])).

fof(f1923,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_151 ),
    inference(resolution,[],[f1903,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1903,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl3_151 ),
    inference(avatar_component_clause,[],[f1902])).

fof(f1904,plain,
    ( spl3_151
    | ~ spl3_39
    | ~ spl3_146 ),
    inference(avatar_split_clause,[],[f1865,f1855,f530,f1902])).

fof(f530,plain,
    ( spl3_39
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f1855,plain,
    ( spl3_146
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_146])])).

fof(f1865,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))
    | ~ spl3_39
    | ~ spl3_146 ),
    inference(resolution,[],[f1856,f535])).

fof(f535,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(k1_tops_1(sK0,sK1),X0) )
    | ~ spl3_39 ),
    inference(resolution,[],[f531,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f531,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f530])).

fof(f1856,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_146 ),
    inference(avatar_component_clause,[],[f1855])).

fof(f1879,plain,
    ( spl3_148
    | ~ spl3_146 ),
    inference(avatar_split_clause,[],[f1870,f1855,f1877])).

fof(f1870,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_146 ),
    inference(resolution,[],[f1856,f79])).

fof(f1857,plain,
    ( spl3_146
    | ~ spl3_32
    | ~ spl3_124 ),
    inference(avatar_split_clause,[],[f1848,f1355,f367,f1855])).

fof(f367,plain,
    ( spl3_32
  <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f1355,plain,
    ( spl3_124
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_124])])).

fof(f1848,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_32
    | ~ spl3_124 ),
    inference(forward_demodulation,[],[f1844,f1356])).

fof(f1356,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_124 ),
    inference(avatar_component_clause,[],[f1355])).

fof(f1844,plain,
    ( r1_tarski(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)))
    | ~ spl3_32 ),
    inference(resolution,[],[f526,f101])).

fof(f101,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f526,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X0)
        | r1_tarski(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),X0)) )
    | ~ spl3_32 ),
    inference(superposition,[],[f81,f368])).

fof(f368,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f367])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1362,plain,
    ( spl3_125
    | ~ spl3_8
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f704,f335,f165,f1360])).

fof(f165,plain,
    ( spl3_8
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f335,plain,
    ( spl3_26
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f704,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_8
    | ~ spl3_26 ),
    inference(superposition,[],[f180,f336])).

fof(f336,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f335])).

fof(f180,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1)
    | ~ spl3_8 ),
    inference(resolution,[],[f166,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f166,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f165])).

fof(f1357,plain,
    ( spl3_124
    | ~ spl3_32
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f528,f441,f367,f1355])).

fof(f441,plain,
    ( spl3_36
  <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f528,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_32
    | ~ spl3_36 ),
    inference(forward_demodulation,[],[f527,f442])).

fof(f442,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f441])).

fof(f527,plain,
    ( k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f525,f97])).

fof(f97,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f525,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_32 ),
    inference(superposition,[],[f84,f368])).

fof(f84,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1063,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f947,plain,
    ( spl3_78
    | ~ spl3_46
    | ~ spl3_70 ),
    inference(avatar_split_clause,[],[f906,f862,f580,f945])).

fof(f580,plain,
    ( spl3_46
  <=> sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f862,plain,
    ( spl3_70
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f906,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_46
    | ~ spl3_70 ),
    inference(forward_demodulation,[],[f902,f581])).

fof(f581,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f580])).

fof(f902,plain,
    ( k1_tops_1(sK0,sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_70 ),
    inference(resolution,[],[f863,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f863,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f862])).

fof(f864,plain,
    ( spl3_70
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f857,f147,f111,f107,f862])).

fof(f107,plain,
    ( spl3_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f111,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f147,plain,
    ( spl3_5
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f857,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f855,f101])).

fof(f855,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f836,f112])).

fof(f112,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f836,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0)) )
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f137,f148])).

fof(f148,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f147])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK1,sK0)
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0)) )
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f121,f108])).

fof(f108,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f107])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK1,sK0)
        | ~ r1_tarski(sK1,X0)
        | r1_tarski(sK1,k1_tops_1(sK0,X0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f112,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f833,plain,
    ( spl3_69
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f703,f165,f150,f831])).

fof(f150,plain,
    ( spl3_6
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f703,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f180,f151])).

fof(f151,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f150])).

fof(f745,plain,
    ( spl3_51
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f731,f700,f107,f103,f743])).

fof(f743,plain,
    ( spl3_51
  <=> v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f103,plain,
    ( spl3_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f700,plain,
    ( spl3_49
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f731,plain,
    ( v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f730,f104])).

fof(f104,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f730,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ spl3_2
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f714,f108])).

fof(f714,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)
    | ~ spl3_49 ),
    inference(resolution,[],[f701,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f701,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f700])).

fof(f702,plain,
    ( spl3_49
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f698,f688,f700])).

fof(f688,plain,
    ( spl3_47
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f698,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_47 ),
    inference(resolution,[],[f689,f79])).

fof(f689,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f688])).

fof(f690,plain,
    ( spl3_47
    | ~ spl3_4
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f686,f530,f143,f688])).

fof(f143,plain,
    ( spl3_4
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f686,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_4
    | ~ spl3_39 ),
    inference(resolution,[],[f535,f144])).

fof(f144,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f143])).

fof(f582,plain,
    ( spl3_46
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f569,f562,f580])).

fof(f562,plain,
    ( spl3_43
  <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f569,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_43 ),
    inference(superposition,[],[f563,f97])).

fof(f563,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f562])).

fof(f564,plain,
    ( spl3_43
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f533,f530,f562])).

fof(f533,plain,
    ( sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_39 ),
    inference(resolution,[],[f531,f95])).

fof(f532,plain,
    ( spl3_39
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f524,f367,f530])).

fof(f524,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_32 ),
    inference(superposition,[],[f86,f368])).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f443,plain,
    ( spl3_36
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f353,f314,f169,f111,f441])).

fof(f169,plain,
    ( spl3_9
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f314,plain,
    ( spl3_21
  <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f353,plain,
    ( k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_9
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f348,f315])).

fof(f315,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f314])).

fof(f348,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_9 ),
    inference(resolution,[],[f125,f170])).

fof(f170,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f169])).

fof(f125,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(sK1,X2) = k4_subset_1(u1_struct_0(sK0),sK1,X2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f112,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f369,plain,
    ( spl3_32
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f328,f310,f111,f367])).

fof(f310,plain,
    ( spl3_20
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f328,plain,
    ( k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(superposition,[],[f311,f122])).

fof(f122,plain,
    ( ! [X1] : k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)
    | ~ spl3_3 ),
    inference(resolution,[],[f112,f69])).

fof(f311,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f310])).

fof(f337,plain,
    ( spl3_26
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f129,f111,f107,f335])).

fof(f129,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f114,f108])).

fof(f114,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f112,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f316,plain,
    ( spl3_21
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f132,f111,f107,f314])).

fof(f132,plain,
    ( k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f117,f108])).

fof(f117,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f112,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f312,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f130,f111,f107,f310])).

fof(f130,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f115,f108])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_3 ),
    inference(resolution,[],[f112,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f171,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f133,f111,f107,f169])).

fof(f133,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f118,f108])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(resolution,[],[f112,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f167,plain,
    ( spl3_8
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f131,f111,f107,f165])).

fof(f131,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f116,f108])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(resolution,[],[f112,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f155,plain,
    ( ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f153,f150,f147])).

fof(f153,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f65,f151])).

fof(f65,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f36,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f152,plain,
    ( spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f64,f150,f147])).

fof(f64,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f145,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f123,f111,f143])).

fof(f123,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f112,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f113,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f66,f111])).

fof(f66,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f39])).

fof(f109,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f68,f107])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).

fof(f105,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f67,f103])).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f39])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:54:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (26844)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.50  % (26852)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.50  % (26836)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.50  % (26835)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (26834)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (26843)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.22/0.52  % (26837)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.52  % (26842)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.22/0.52  % (26853)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.22/0.53  % (26851)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.22/0.53  % (26850)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.22/0.53  % (26855)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.22/0.53  % (26847)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.22/0.53  % (26845)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.22/0.53  % (26858)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.22/0.53  % (26838)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.22/0.53  % (26857)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.22/0.53  % (26833)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.53  % (26832)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.54  % (26839)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.54  % (26854)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.54  % (26856)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.54  % (26860)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.54  % (26849)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.34/0.54  % (26846)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.54  % (26840)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.54  % (26861)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.55  % (26848)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.34/0.55  % (26841)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.55  % (26859)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 2.58/0.72  % (26858)Refutation found. Thanks to Tanya!
% 2.58/0.72  % SZS status Theorem for theBenchmark
% 2.58/0.72  % SZS output start Proof for theBenchmark
% 2.58/0.72  fof(f2129,plain,(
% 2.58/0.72    $false),
% 2.58/0.72    inference(avatar_sat_refutation,[],[f105,f109,f113,f145,f152,f155,f167,f171,f312,f316,f337,f369,f443,f532,f564,f582,f690,f702,f745,f833,f864,f947,f1063,f1357,f1362,f1857,f1879,f1904,f2009,f2127,f2128])).
% 2.58/0.72  fof(f2128,plain,(
% 2.58/0.72    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)),
% 2.58/0.72    introduced(theory_tautology_sat_conflict,[])).
% 2.58/0.72  fof(f2127,plain,(
% 2.58/0.72    spl3_78 | ~spl3_69 | ~spl3_125 | ~spl3_148 | ~spl3_156),
% 2.58/0.72    inference(avatar_split_clause,[],[f2093,f2007,f1877,f1360,f831,f945])).
% 2.58/0.72  fof(f945,plain,(
% 2.58/0.72    spl3_78 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 2.58/0.72  fof(f831,plain,(
% 2.58/0.72    spl3_69 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 2.58/0.72  fof(f1360,plain,(
% 2.58/0.72    spl3_125 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_125])])).
% 2.58/0.72  fof(f1877,plain,(
% 2.58/0.72    spl3_148 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_148])])).
% 2.58/0.72  fof(f2007,plain,(
% 2.58/0.72    spl3_156 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_156])])).
% 2.58/0.72  fof(f2093,plain,(
% 2.58/0.72    sK1 = k1_tops_1(sK0,sK1) | (~spl3_69 | ~spl3_125 | ~spl3_148 | ~spl3_156)),
% 2.58/0.72    inference(forward_demodulation,[],[f2092,f1895])).
% 2.58/0.72  fof(f1895,plain,(
% 2.58/0.72    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl3_69 | ~spl3_148)),
% 2.58/0.72    inference(forward_demodulation,[],[f1890,f1892])).
% 2.58/0.72  fof(f1892,plain,(
% 2.58/0.72    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | (~spl3_69 | ~spl3_148)),
% 2.58/0.72    inference(forward_demodulation,[],[f1887,f832])).
% 2.58/0.72  fof(f832,plain,(
% 2.58/0.72    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_69),
% 2.58/0.72    inference(avatar_component_clause,[],[f831])).
% 2.58/0.72  fof(f1887,plain,(
% 2.58/0.72    k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),sK1) | ~spl3_148),
% 2.58/0.72    inference(resolution,[],[f1878,f83])).
% 2.58/0.72  fof(f83,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 2.58/0.72    inference(cnf_transformation,[],[f55])).
% 2.58/0.72  fof(f55,plain,(
% 2.58/0.72    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.58/0.72    inference(ennf_transformation,[],[f17])).
% 2.58/0.72  fof(f17,axiom,(
% 2.58/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.58/0.72  fof(f1878,plain,(
% 2.58/0.72    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_148),
% 2.58/0.72    inference(avatar_component_clause,[],[f1877])).
% 2.58/0.72  fof(f1890,plain,(
% 2.58/0.72    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),sK1)) | ~spl3_148),
% 2.58/0.72    inference(resolution,[],[f1878,f89])).
% 2.58/0.72  fof(f89,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 2.58/0.72    inference(cnf_transformation,[],[f59])).
% 2.58/0.72  fof(f59,plain,(
% 2.58/0.72    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.58/0.72    inference(ennf_transformation,[],[f21])).
% 2.58/0.72  fof(f21,axiom,(
% 2.58/0.72    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.58/0.72  fof(f2092,plain,(
% 2.58/0.72    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl3_125 | ~spl3_156)),
% 2.58/0.72    inference(forward_demodulation,[],[f2087,f2089])).
% 2.58/0.72  fof(f2089,plain,(
% 2.58/0.72    k2_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl3_125 | ~spl3_156)),
% 2.58/0.72    inference(forward_demodulation,[],[f2084,f1361])).
% 2.58/0.72  fof(f1361,plain,(
% 2.58/0.72    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl3_125),
% 2.58/0.72    inference(avatar_component_clause,[],[f1360])).
% 2.58/0.72  fof(f2084,plain,(
% 2.58/0.72    k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) = k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl3_156),
% 2.58/0.72    inference(resolution,[],[f2008,f83])).
% 2.58/0.72  fof(f2008,plain,(
% 2.58/0.72    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_156),
% 2.58/0.72    inference(avatar_component_clause,[],[f2007])).
% 2.58/0.72  fof(f2087,plain,(
% 2.58/0.72    k1_tops_1(sK0,sK1) = k3_subset_1(k2_pre_topc(sK0,sK1),k3_subset_1(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl3_156),
% 2.58/0.72    inference(resolution,[],[f2008,f89])).
% 2.58/0.72  fof(f2009,plain,(
% 2.58/0.72    spl3_156 | ~spl3_151),
% 2.58/0.72    inference(avatar_split_clause,[],[f1923,f1902,f2007])).
% 2.58/0.72  fof(f1902,plain,(
% 2.58/0.72    spl3_151 <=> r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_151])])).
% 2.58/0.72  fof(f1923,plain,(
% 2.58/0.72    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_151),
% 2.58/0.72    inference(resolution,[],[f1903,f79])).
% 2.58/0.72  fof(f79,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.58/0.72    inference(cnf_transformation,[],[f27])).
% 2.58/0.72  fof(f27,axiom,(
% 2.58/0.72    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.58/0.72  fof(f1903,plain,(
% 2.58/0.72    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | ~spl3_151),
% 2.58/0.72    inference(avatar_component_clause,[],[f1902])).
% 2.58/0.72  fof(f1904,plain,(
% 2.58/0.72    spl3_151 | ~spl3_39 | ~spl3_146),
% 2.58/0.72    inference(avatar_split_clause,[],[f1865,f1855,f530,f1902])).
% 2.58/0.72  fof(f530,plain,(
% 2.58/0.72    spl3_39 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 2.58/0.72  fof(f1855,plain,(
% 2.58/0.72    spl3_146 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_146])])).
% 2.58/0.72  fof(f1865,plain,(
% 2.58/0.72    r1_tarski(k1_tops_1(sK0,sK1),k2_pre_topc(sK0,sK1)) | (~spl3_39 | ~spl3_146)),
% 2.58/0.72    inference(resolution,[],[f1856,f535])).
% 2.58/0.72  fof(f535,plain,(
% 2.58/0.72    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) ) | ~spl3_39),
% 2.58/0.72    inference(resolution,[],[f531,f91])).
% 2.58/0.72  fof(f91,plain,(
% 2.58/0.72    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 2.58/0.72    inference(cnf_transformation,[],[f62])).
% 2.58/0.72  fof(f62,plain,(
% 2.58/0.72    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.58/0.72    inference(flattening,[],[f61])).
% 2.58/0.72  fof(f61,plain,(
% 2.58/0.72    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.58/0.72    inference(ennf_transformation,[],[f8])).
% 2.58/0.72  fof(f8,axiom,(
% 2.58/0.72    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.58/0.72  fof(f531,plain,(
% 2.58/0.72    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_39),
% 2.58/0.72    inference(avatar_component_clause,[],[f530])).
% 2.58/0.72  fof(f1856,plain,(
% 2.58/0.72    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_146),
% 2.58/0.72    inference(avatar_component_clause,[],[f1855])).
% 2.58/0.72  fof(f1879,plain,(
% 2.58/0.72    spl3_148 | ~spl3_146),
% 2.58/0.72    inference(avatar_split_clause,[],[f1870,f1855,f1877])).
% 2.58/0.72  fof(f1870,plain,(
% 2.58/0.72    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_146),
% 2.58/0.72    inference(resolution,[],[f1856,f79])).
% 2.58/0.72  fof(f1857,plain,(
% 2.58/0.72    spl3_146 | ~spl3_32 | ~spl3_124),
% 2.58/0.72    inference(avatar_split_clause,[],[f1848,f1355,f367,f1855])).
% 2.58/0.72  fof(f367,plain,(
% 2.58/0.72    spl3_32 <=> k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.58/0.72  fof(f1355,plain,(
% 2.58/0.72    spl3_124 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_124])])).
% 2.58/0.72  fof(f1848,plain,(
% 2.58/0.72    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_32 | ~spl3_124)),
% 2.58/0.72    inference(forward_demodulation,[],[f1844,f1356])).
% 2.58/0.72  fof(f1356,plain,(
% 2.58/0.72    k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl3_124),
% 2.58/0.72    inference(avatar_component_clause,[],[f1355])).
% 2.58/0.72  fof(f1844,plain,(
% 2.58/0.72    r1_tarski(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1))) | ~spl3_32),
% 2.58/0.72    inference(resolution,[],[f526,f101])).
% 2.58/0.72  fof(f101,plain,(
% 2.58/0.72    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.58/0.72    inference(equality_resolution,[],[f92])).
% 2.58/0.72  fof(f92,plain,(
% 2.58/0.72    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.58/0.72    inference(cnf_transformation,[],[f3])).
% 2.58/0.72  fof(f3,axiom,(
% 2.58/0.72    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.58/0.72  fof(f526,plain,(
% 2.58/0.72    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK1),X0) | r1_tarski(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),X0))) ) | ~spl3_32),
% 2.58/0.72    inference(superposition,[],[f81,f368])).
% 2.58/0.72  fof(f368,plain,(
% 2.58/0.72    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_32),
% 2.58/0.72    inference(avatar_component_clause,[],[f367])).
% 2.58/0.72  fof(f81,plain,(
% 2.58/0.72    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 2.58/0.72    inference(cnf_transformation,[],[f53])).
% 2.58/0.72  fof(f53,plain,(
% 2.58/0.72    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.58/0.72    inference(ennf_transformation,[],[f13])).
% 2.58/0.72  fof(f13,axiom,(
% 2.58/0.72    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.58/0.72  fof(f1362,plain,(
% 2.58/0.72    spl3_125 | ~spl3_8 | ~spl3_26),
% 2.58/0.72    inference(avatar_split_clause,[],[f704,f335,f165,f1360])).
% 2.58/0.72  fof(f165,plain,(
% 2.58/0.72    spl3_8 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.58/0.72  fof(f335,plain,(
% 2.58/0.72    spl3_26 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.58/0.72  fof(f704,plain,(
% 2.58/0.72    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl3_8 | ~spl3_26)),
% 2.58/0.72    inference(superposition,[],[f180,f336])).
% 2.58/0.72  fof(f336,plain,(
% 2.58/0.72    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl3_26),
% 2.58/0.72    inference(avatar_component_clause,[],[f335])).
% 2.58/0.72  fof(f180,plain,(
% 2.58/0.72    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),X1) = k4_xboole_0(k2_pre_topc(sK0,sK1),X1)) ) | ~spl3_8),
% 2.58/0.72    inference(resolution,[],[f166,f69])).
% 2.58/0.72  fof(f69,plain,(
% 2.58/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 2.58/0.72    inference(cnf_transformation,[],[f40])).
% 2.58/0.72  fof(f40,plain,(
% 2.58/0.72    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.58/0.72    inference(ennf_transformation,[],[f23])).
% 2.58/0.72  fof(f23,axiom,(
% 2.58/0.72    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.58/0.72  fof(f166,plain,(
% 2.58/0.72    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_8),
% 2.58/0.72    inference(avatar_component_clause,[],[f165])).
% 2.58/0.72  fof(f1357,plain,(
% 2.58/0.72    spl3_124 | ~spl3_32 | ~spl3_36),
% 2.58/0.72    inference(avatar_split_clause,[],[f528,f441,f367,f1355])).
% 2.58/0.72  fof(f441,plain,(
% 2.58/0.72    spl3_36 <=> k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 2.58/0.72  fof(f528,plain,(
% 2.58/0.72    k2_pre_topc(sK0,sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl3_32 | ~spl3_36)),
% 2.58/0.72    inference(forward_demodulation,[],[f527,f442])).
% 2.58/0.72  fof(f442,plain,(
% 2.58/0.72    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_36),
% 2.58/0.72    inference(avatar_component_clause,[],[f441])).
% 2.58/0.72  fof(f527,plain,(
% 2.58/0.72    k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl3_32),
% 2.58/0.72    inference(forward_demodulation,[],[f525,f97])).
% 2.58/0.72  fof(f97,plain,(
% 2.58/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.58/0.72    inference(cnf_transformation,[],[f1])).
% 2.58/0.72  fof(f1,axiom,(
% 2.58/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.58/0.72  fof(f525,plain,(
% 2.58/0.72    k2_xboole_0(k2_tops_1(sK0,sK1),sK1) = k2_xboole_0(k2_tops_1(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl3_32),
% 2.58/0.72    inference(superposition,[],[f84,f368])).
% 2.58/0.72  fof(f84,plain,(
% 2.58/0.72    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.58/0.72    inference(cnf_transformation,[],[f11])).
% 2.58/0.72  fof(f11,axiom,(
% 2.58/0.72    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.58/0.72  fof(f1063,plain,(
% 2.58/0.72    sK1 != k1_tops_1(sK0,sK1) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.58/0.72    introduced(theory_tautology_sat_conflict,[])).
% 2.58/0.72  fof(f947,plain,(
% 2.58/0.72    spl3_78 | ~spl3_46 | ~spl3_70),
% 2.58/0.72    inference(avatar_split_clause,[],[f906,f862,f580,f945])).
% 2.58/0.72  fof(f580,plain,(
% 2.58/0.72    spl3_46 <=> sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 2.58/0.72  fof(f862,plain,(
% 2.58/0.72    spl3_70 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 2.58/0.72  fof(f906,plain,(
% 2.58/0.72    sK1 = k1_tops_1(sK0,sK1) | (~spl3_46 | ~spl3_70)),
% 2.58/0.72    inference(forward_demodulation,[],[f902,f581])).
% 2.58/0.72  fof(f581,plain,(
% 2.58/0.72    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl3_46),
% 2.58/0.72    inference(avatar_component_clause,[],[f580])).
% 2.58/0.72  fof(f902,plain,(
% 2.58/0.72    k1_tops_1(sK0,sK1) = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl3_70),
% 2.58/0.72    inference(resolution,[],[f863,f95])).
% 2.58/0.72  fof(f95,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.58/0.72    inference(cnf_transformation,[],[f63])).
% 2.58/0.72  fof(f63,plain,(
% 2.58/0.72    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.58/0.72    inference(ennf_transformation,[],[f6])).
% 2.58/0.72  fof(f6,axiom,(
% 2.58/0.72    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.58/0.72  fof(f863,plain,(
% 2.58/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl3_70),
% 2.58/0.72    inference(avatar_component_clause,[],[f862])).
% 2.58/0.72  fof(f864,plain,(
% 2.58/0.72    spl3_70 | ~spl3_2 | ~spl3_3 | ~spl3_5),
% 2.58/0.72    inference(avatar_split_clause,[],[f857,f147,f111,f107,f862])).
% 2.58/0.72  fof(f107,plain,(
% 2.58/0.72    spl3_2 <=> l1_pre_topc(sK0)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.58/0.72  fof(f111,plain,(
% 2.58/0.72    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.58/0.72  fof(f147,plain,(
% 2.58/0.72    spl3_5 <=> v3_pre_topc(sK1,sK0)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.58/0.72  fof(f857,plain,(
% 2.58/0.72    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_5)),
% 2.58/0.72    inference(subsumption_resolution,[],[f855,f101])).
% 2.58/0.72  fof(f855,plain,(
% 2.58/0.72    ~r1_tarski(sK1,sK1) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_5)),
% 2.58/0.72    inference(resolution,[],[f836,f112])).
% 2.58/0.72  fof(f112,plain,(
% 2.58/0.72    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.58/0.72    inference(avatar_component_clause,[],[f111])).
% 2.58/0.72  fof(f836,plain,(
% 2.58/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0))) ) | (~spl3_2 | ~spl3_3 | ~spl3_5)),
% 2.58/0.72    inference(subsumption_resolution,[],[f137,f148])).
% 2.58/0.72  fof(f148,plain,(
% 2.58/0.72    v3_pre_topc(sK1,sK0) | ~spl3_5),
% 2.58/0.72    inference(avatar_component_clause,[],[f147])).
% 2.58/0.72  fof(f137,plain,(
% 2.58/0.72    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0))) ) | (~spl3_2 | ~spl3_3)),
% 2.58/0.72    inference(subsumption_resolution,[],[f121,f108])).
% 2.58/0.72  fof(f108,plain,(
% 2.58/0.72    l1_pre_topc(sK0) | ~spl3_2),
% 2.58/0.72    inference(avatar_component_clause,[],[f107])).
% 2.58/0.72  fof(f121,plain,(
% 2.58/0.72    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,X0) | r1_tarski(sK1,k1_tops_1(sK0,X0))) ) | ~spl3_3),
% 2.58/0.72    inference(resolution,[],[f112,f77])).
% 2.58/0.72  fof(f77,plain,(
% 2.58/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 2.58/0.72    inference(cnf_transformation,[],[f52])).
% 2.58/0.72  fof(f52,plain,(
% 2.58/0.72    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.72    inference(flattening,[],[f51])).
% 2.58/0.72  fof(f51,plain,(
% 2.58/0.72    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.72    inference(ennf_transformation,[],[f32])).
% 2.58/0.72  fof(f32,axiom,(
% 2.58/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 2.58/0.72  fof(f833,plain,(
% 2.58/0.72    spl3_69 | ~spl3_6 | ~spl3_8),
% 2.58/0.72    inference(avatar_split_clause,[],[f703,f165,f150,f831])).
% 2.58/0.72  fof(f150,plain,(
% 2.58/0.72    spl3_6 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.58/0.72  fof(f703,plain,(
% 2.58/0.72    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_6 | ~spl3_8)),
% 2.58/0.72    inference(superposition,[],[f180,f151])).
% 2.58/0.72  fof(f151,plain,(
% 2.58/0.72    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_6),
% 2.58/0.72    inference(avatar_component_clause,[],[f150])).
% 2.58/0.72  fof(f745,plain,(
% 2.58/0.72    spl3_51 | ~spl3_1 | ~spl3_2 | ~spl3_49),
% 2.58/0.72    inference(avatar_split_clause,[],[f731,f700,f107,f103,f743])).
% 2.58/0.72  fof(f743,plain,(
% 2.58/0.72    spl3_51 <=> v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 2.58/0.72  fof(f103,plain,(
% 2.58/0.72    spl3_1 <=> v2_pre_topc(sK0)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.58/0.72  fof(f700,plain,(
% 2.58/0.72    spl3_49 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 2.58/0.72  fof(f731,plain,(
% 2.58/0.72    v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) | (~spl3_1 | ~spl3_2 | ~spl3_49)),
% 2.58/0.72    inference(subsumption_resolution,[],[f730,f104])).
% 2.58/0.72  fof(f104,plain,(
% 2.58/0.72    v2_pre_topc(sK0) | ~spl3_1),
% 2.58/0.72    inference(avatar_component_clause,[],[f103])).
% 2.58/0.72  fof(f730,plain,(
% 2.58/0.72    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) | (~spl3_2 | ~spl3_49)),
% 2.58/0.72    inference(subsumption_resolution,[],[f714,f108])).
% 2.58/0.72  fof(f714,plain,(
% 2.58/0.72    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,k1_tops_1(sK0,sK1)),sK0) | ~spl3_49),
% 2.58/0.72    inference(resolution,[],[f701,f76])).
% 2.58/0.72  fof(f76,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 2.58/0.72    inference(cnf_transformation,[],[f50])).
% 2.58/0.72  fof(f50,plain,(
% 2.58/0.72    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.58/0.72    inference(flattening,[],[f49])).
% 2.58/0.72  fof(f49,plain,(
% 2.58/0.72    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.58/0.72    inference(ennf_transformation,[],[f30])).
% 2.58/0.72  fof(f30,axiom,(
% 2.58/0.72    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.58/0.72  fof(f701,plain,(
% 2.58/0.72    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_49),
% 2.58/0.72    inference(avatar_component_clause,[],[f700])).
% 2.58/0.72  fof(f702,plain,(
% 2.58/0.72    spl3_49 | ~spl3_47),
% 2.58/0.72    inference(avatar_split_clause,[],[f698,f688,f700])).
% 2.58/0.72  fof(f688,plain,(
% 2.58/0.72    spl3_47 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 2.58/0.72  fof(f698,plain,(
% 2.58/0.72    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_47),
% 2.58/0.72    inference(resolution,[],[f689,f79])).
% 2.58/0.72  fof(f689,plain,(
% 2.58/0.72    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl3_47),
% 2.58/0.72    inference(avatar_component_clause,[],[f688])).
% 2.58/0.72  fof(f690,plain,(
% 2.58/0.72    spl3_47 | ~spl3_4 | ~spl3_39),
% 2.58/0.72    inference(avatar_split_clause,[],[f686,f530,f143,f688])).
% 2.58/0.72  fof(f143,plain,(
% 2.58/0.72    spl3_4 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.58/0.72  fof(f686,plain,(
% 2.58/0.72    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | (~spl3_4 | ~spl3_39)),
% 2.58/0.72    inference(resolution,[],[f535,f144])).
% 2.58/0.72  fof(f144,plain,(
% 2.58/0.72    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_4),
% 2.58/0.72    inference(avatar_component_clause,[],[f143])).
% 2.58/0.72  fof(f582,plain,(
% 2.58/0.72    spl3_46 | ~spl3_43),
% 2.58/0.72    inference(avatar_split_clause,[],[f569,f562,f580])).
% 2.58/0.72  fof(f562,plain,(
% 2.58/0.72    spl3_43 <=> sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 2.58/0.72  fof(f569,plain,(
% 2.58/0.72    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl3_43),
% 2.58/0.72    inference(superposition,[],[f563,f97])).
% 2.58/0.72  fof(f563,plain,(
% 2.58/0.72    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl3_43),
% 2.58/0.72    inference(avatar_component_clause,[],[f562])).
% 2.58/0.72  fof(f564,plain,(
% 2.58/0.72    spl3_43 | ~spl3_39),
% 2.58/0.72    inference(avatar_split_clause,[],[f533,f530,f562])).
% 2.58/0.72  fof(f533,plain,(
% 2.58/0.72    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) | ~spl3_39),
% 2.58/0.72    inference(resolution,[],[f531,f95])).
% 2.58/0.72  fof(f532,plain,(
% 2.58/0.72    spl3_39 | ~spl3_32),
% 2.58/0.72    inference(avatar_split_clause,[],[f524,f367,f530])).
% 2.58/0.72  fof(f524,plain,(
% 2.58/0.72    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_32),
% 2.58/0.72    inference(superposition,[],[f86,f368])).
% 2.58/0.72  fof(f86,plain,(
% 2.58/0.72    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.58/0.72    inference(cnf_transformation,[],[f10])).
% 2.58/0.72  fof(f10,axiom,(
% 2.58/0.72    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.58/0.72  fof(f443,plain,(
% 2.58/0.72    spl3_36 | ~spl3_3 | ~spl3_9 | ~spl3_21),
% 2.58/0.72    inference(avatar_split_clause,[],[f353,f314,f169,f111,f441])).
% 2.58/0.72  fof(f169,plain,(
% 2.58/0.72    spl3_9 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.58/0.72  fof(f314,plain,(
% 2.58/0.72    spl3_21 <=> k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.58/0.72  fof(f353,plain,(
% 2.58/0.72    k2_pre_topc(sK0,sK1) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_9 | ~spl3_21)),
% 2.58/0.72    inference(forward_demodulation,[],[f348,f315])).
% 2.58/0.72  fof(f315,plain,(
% 2.58/0.72    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_21),
% 2.58/0.72    inference(avatar_component_clause,[],[f314])).
% 2.58/0.72  fof(f348,plain,(
% 2.58/0.72    k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k2_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_9)),
% 2.58/0.72    inference(resolution,[],[f125,f170])).
% 2.58/0.72  fof(f170,plain,(
% 2.58/0.72    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 2.58/0.72    inference(avatar_component_clause,[],[f169])).
% 2.58/0.72  fof(f125,plain,(
% 2.58/0.72    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(sK1,X2) = k4_subset_1(u1_struct_0(sK0),sK1,X2)) ) | ~spl3_3),
% 2.58/0.72    inference(resolution,[],[f112,f87])).
% 2.58/0.72  fof(f87,plain,(
% 2.58/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 2.58/0.72    inference(cnf_transformation,[],[f57])).
% 2.58/0.72  fof(f57,plain,(
% 2.58/0.72    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.58/0.72    inference(flattening,[],[f56])).
% 2.58/0.72  fof(f56,plain,(
% 2.58/0.72    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.58/0.72    inference(ennf_transformation,[],[f22])).
% 2.58/0.72  fof(f22,axiom,(
% 2.58/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.58/0.72  fof(f369,plain,(
% 2.58/0.72    spl3_32 | ~spl3_3 | ~spl3_20),
% 2.58/0.72    inference(avatar_split_clause,[],[f328,f310,f111,f367])).
% 2.58/0.72  fof(f310,plain,(
% 2.58/0.72    spl3_20 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 2.58/0.72    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.58/0.72  fof(f328,plain,(
% 2.58/0.72    k1_tops_1(sK0,sK1) = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_3 | ~spl3_20)),
% 2.58/0.72    inference(superposition,[],[f311,f122])).
% 2.58/0.72  fof(f122,plain,(
% 2.58/0.72    ( ! [X1] : (k7_subset_1(u1_struct_0(sK0),sK1,X1) = k4_xboole_0(sK1,X1)) ) | ~spl3_3),
% 2.58/0.72    inference(resolution,[],[f112,f69])).
% 2.58/0.72  fof(f311,plain,(
% 2.58/0.72    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_20),
% 2.58/0.72    inference(avatar_component_clause,[],[f310])).
% 2.58/0.72  fof(f337,plain,(
% 2.58/0.72    spl3_26 | ~spl3_2 | ~spl3_3),
% 2.58/0.72    inference(avatar_split_clause,[],[f129,f111,f107,f335])).
% 2.58/0.72  fof(f129,plain,(
% 2.58/0.72    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3)),
% 2.58/0.72    inference(subsumption_resolution,[],[f114,f108])).
% 2.58/0.72  fof(f114,plain,(
% 2.58/0.72    ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) | ~spl3_3),
% 2.58/0.72    inference(resolution,[],[f112,f70])).
% 2.58/0.72  fof(f70,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 2.58/0.72    inference(cnf_transformation,[],[f41])).
% 2.58/0.72  fof(f41,plain,(
% 2.58/0.72    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.72    inference(ennf_transformation,[],[f31])).
% 2.58/0.72  fof(f31,axiom,(
% 2.58/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.58/0.72  fof(f316,plain,(
% 2.58/0.72    spl3_21 | ~spl3_2 | ~spl3_3),
% 2.58/0.72    inference(avatar_split_clause,[],[f132,f111,f107,f314])).
% 2.58/0.72  fof(f132,plain,(
% 2.58/0.72    k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3)),
% 2.58/0.72    inference(subsumption_resolution,[],[f117,f108])).
% 2.58/0.72  fof(f117,plain,(
% 2.58/0.72    ~l1_pre_topc(sK0) | k2_pre_topc(sK0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_3),
% 2.58/0.72    inference(resolution,[],[f112,f73])).
% 2.58/0.72  fof(f73,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.58/0.72    inference(cnf_transformation,[],[f45])).
% 2.58/0.72  fof(f45,plain,(
% 2.58/0.72    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.72    inference(ennf_transformation,[],[f34])).
% 2.58/0.72  fof(f34,axiom,(
% 2.58/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 2.58/0.72  fof(f312,plain,(
% 2.58/0.72    spl3_20 | ~spl3_2 | ~spl3_3),
% 2.58/0.72    inference(avatar_split_clause,[],[f130,f111,f107,f310])).
% 2.58/0.72  fof(f130,plain,(
% 2.58/0.72    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl3_2 | ~spl3_3)),
% 2.58/0.72    inference(subsumption_resolution,[],[f115,f108])).
% 2.58/0.72  fof(f115,plain,(
% 2.58/0.72    ~l1_pre_topc(sK0) | k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | ~spl3_3),
% 2.58/0.72    inference(resolution,[],[f112,f71])).
% 2.58/0.72  fof(f71,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.58/0.72    inference(cnf_transformation,[],[f42])).
% 2.58/0.72  fof(f42,plain,(
% 2.58/0.72    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.58/0.72    inference(ennf_transformation,[],[f35])).
% 2.58/0.72  fof(f35,axiom,(
% 2.58/0.72    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.58/0.72  fof(f171,plain,(
% 2.58/0.72    spl3_9 | ~spl3_2 | ~spl3_3),
% 2.58/0.72    inference(avatar_split_clause,[],[f133,f111,f107,f169])).
% 2.58/0.72  fof(f133,plain,(
% 2.58/0.72    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3)),
% 2.58/0.72    inference(subsumption_resolution,[],[f118,f108])).
% 2.58/0.72  fof(f118,plain,(
% 2.58/0.72    ~l1_pre_topc(sK0) | m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.58/0.72    inference(resolution,[],[f112,f74])).
% 2.58/0.72  fof(f74,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.58/0.72    inference(cnf_transformation,[],[f47])).
% 2.58/0.72  fof(f47,plain,(
% 2.58/0.72    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.58/0.72    inference(flattening,[],[f46])).
% 2.58/0.72  fof(f46,plain,(
% 2.58/0.72    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.58/0.72    inference(ennf_transformation,[],[f29])).
% 2.58/0.72  fof(f29,axiom,(
% 2.58/0.72    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.58/0.72  fof(f167,plain,(
% 2.58/0.72    spl3_8 | ~spl3_2 | ~spl3_3),
% 2.58/0.72    inference(avatar_split_clause,[],[f131,f111,f107,f165])).
% 2.58/0.72  fof(f131,plain,(
% 2.58/0.72    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_3)),
% 2.58/0.72    inference(subsumption_resolution,[],[f116,f108])).
% 2.58/0.72  fof(f116,plain,(
% 2.58/0.72    ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.58/0.72    inference(resolution,[],[f112,f72])).
% 2.58/0.72  fof(f72,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.58/0.72    inference(cnf_transformation,[],[f44])).
% 2.58/0.72  fof(f44,plain,(
% 2.58/0.72    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.58/0.72    inference(flattening,[],[f43])).
% 2.58/0.72  fof(f43,plain,(
% 2.58/0.72    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.58/0.72    inference(ennf_transformation,[],[f28])).
% 2.58/0.72  fof(f28,axiom,(
% 2.58/0.72    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.58/0.72  fof(f155,plain,(
% 2.58/0.72    ~spl3_5 | ~spl3_6),
% 2.58/0.72    inference(avatar_split_clause,[],[f153,f150,f147])).
% 2.58/0.72  fof(f153,plain,(
% 2.58/0.72    ~v3_pre_topc(sK1,sK0) | ~spl3_6),
% 2.58/0.72    inference(subsumption_resolution,[],[f65,f151])).
% 2.58/0.72  fof(f65,plain,(
% 2.58/0.72    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.58/0.72    inference(cnf_transformation,[],[f39])).
% 2.58/0.72  fof(f39,plain,(
% 2.58/0.72    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.58/0.72    inference(flattening,[],[f38])).
% 2.58/0.72  fof(f38,plain,(
% 2.58/0.72    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.58/0.72    inference(ennf_transformation,[],[f37])).
% 2.58/0.72  fof(f37,negated_conjecture,(
% 2.58/0.72    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.58/0.72    inference(negated_conjecture,[],[f36])).
% 2.58/0.72  fof(f36,conjecture,(
% 2.58/0.72    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.58/0.72    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.58/0.72  fof(f152,plain,(
% 2.58/0.72    spl3_5 | spl3_6),
% 2.58/0.72    inference(avatar_split_clause,[],[f64,f150,f147])).
% 2.58/0.72  fof(f64,plain,(
% 2.58/0.72    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.58/0.72    inference(cnf_transformation,[],[f39])).
% 2.58/0.72  fof(f145,plain,(
% 2.58/0.72    spl3_4 | ~spl3_3),
% 2.58/0.72    inference(avatar_split_clause,[],[f123,f111,f143])).
% 2.58/0.72  fof(f123,plain,(
% 2.58/0.72    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 2.58/0.72    inference(resolution,[],[f112,f80])).
% 2.58/0.72  fof(f80,plain,(
% 2.58/0.72    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.58/0.72    inference(cnf_transformation,[],[f27])).
% 2.58/0.72  fof(f113,plain,(
% 2.58/0.72    spl3_3),
% 2.58/0.72    inference(avatar_split_clause,[],[f66,f111])).
% 2.58/0.72  fof(f66,plain,(
% 2.58/0.72    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.58/0.72    inference(cnf_transformation,[],[f39])).
% 2.58/0.72  fof(f109,plain,(
% 2.58/0.72    spl3_2),
% 2.58/0.72    inference(avatar_split_clause,[],[f68,f107])).
% 2.58/0.72  fof(f68,plain,(
% 2.58/0.72    l1_pre_topc(sK0)),
% 2.58/0.72    inference(cnf_transformation,[],[f39])).
% 2.58/0.72  fof(f105,plain,(
% 2.58/0.72    spl3_1),
% 2.58/0.72    inference(avatar_split_clause,[],[f67,f103])).
% 2.58/0.72  fof(f67,plain,(
% 2.58/0.72    v2_pre_topc(sK0)),
% 2.58/0.72    inference(cnf_transformation,[],[f39])).
% 2.58/0.72  % SZS output end Proof for theBenchmark
% 2.58/0.72  % (26858)------------------------------
% 2.58/0.72  % (26858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.58/0.72  % (26858)Termination reason: Refutation
% 2.58/0.72  
% 2.58/0.72  % (26858)Memory used [KB]: 7803
% 2.58/0.72  % (26858)Time elapsed: 0.294 s
% 2.58/0.72  % (26858)------------------------------
% 2.58/0.72  % (26858)------------------------------
% 2.58/0.74  % (26827)Success in time 0.379 s
%------------------------------------------------------------------------------
