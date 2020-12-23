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
% DateTime   : Thu Dec  3 13:11:11 EST 2020

% Result     : Theorem 1.76s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 206 expanded)
%              Number of leaves         :   30 (  85 expanded)
%              Depth                    :    8
%              Number of atoms          :  286 ( 494 expanded)
%              Number of equality atoms :   18 (  28 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f80,f387,f1362,f1843,f1882,f1908,f1926,f1931,f1937,f1946,f2041,f2055,f2167,f2174])).

fof(f2174,plain,(
    spl3_59 ),
    inference(avatar_contradiction_clause,[],[f2168])).

fof(f2168,plain,
    ( $false
    | spl3_59 ),
    inference(unit_resulting_resolution,[],[f36,f2166,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f2166,plain,
    ( ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | spl3_59 ),
    inference(avatar_component_clause,[],[f2164])).

fof(f2164,plain,
    ( spl3_59
  <=> r1_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f36,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f2167,plain,
    ( ~ spl3_4
    | ~ spl3_59
    | ~ spl3_1
    | spl3_44 ),
    inference(avatar_split_clause,[],[f2158,f2052,f54,f2164,f69])).

fof(f69,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f54,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f2052,plain,
    ( spl3_44
  <=> r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f2158,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r1_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_44 ),
    inference(resolution,[],[f2054,f283])).

fof(f283,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k1_tops_1(X1,X0),X2)
      | ~ l1_pre_topc(X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f34,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f2054,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2))
    | spl3_44 ),
    inference(avatar_component_clause,[],[f2052])).

fof(f2055,plain,
    ( ~ spl3_44
    | spl3_43 ),
    inference(avatar_split_clause,[],[f2049,f2038,f2052])).

fof(f2038,plain,
    ( spl3_43
  <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f2049,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2))
    | spl3_43 ),
    inference(resolution,[],[f2040,f40])).

fof(f2040,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))
    | spl3_43 ),
    inference(avatar_component_clause,[],[f2038])).

fof(f2041,plain,
    ( ~ spl3_31
    | ~ spl3_43
    | ~ spl3_1
    | spl3_29 ),
    inference(avatar_split_clause,[],[f2027,f1905,f54,f2038,f1923])).

fof(f1923,plain,
    ( spl3_31
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f1905,plain,
    ( spl3_29
  <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f2027,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_29 ),
    inference(resolution,[],[f1907,f283])).

fof(f1907,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f1905])).

fof(f1946,plain,
    ( ~ spl3_5
    | spl3_32 ),
    inference(avatar_split_clause,[],[f1940,f1934,f77])).

fof(f77,plain,
    ( spl3_5
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1934,plain,
    ( spl3_32
  <=> r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f1940,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | spl3_32 ),
    inference(superposition,[],[f1938,f87])).

fof(f87,plain,(
    ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1 ),
    inference(resolution,[],[f41,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1938,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK1,sK2),X0),u1_struct_0(sK0))
    | spl3_32 ),
    inference(resolution,[],[f1936,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f1936,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_32 ),
    inference(avatar_component_clause,[],[f1934])).

fof(f1937,plain,
    ( ~ spl3_32
    | spl3_31 ),
    inference(avatar_split_clause,[],[f1932,f1923,f1934])).

fof(f1932,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))
    | spl3_31 ),
    inference(resolution,[],[f1925,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1925,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f1923])).

fof(f1931,plain,(
    spl3_30 ),
    inference(avatar_contradiction_clause,[],[f1927])).

fof(f1927,plain,
    ( $false
    | spl3_30 ),
    inference(unit_resulting_resolution,[],[f37,f1921])).

fof(f1921,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | spl3_30 ),
    inference(avatar_component_clause,[],[f1919])).

fof(f1919,plain,
    ( spl3_30
  <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f1926,plain,
    ( ~ spl3_1
    | ~ spl3_30
    | ~ spl3_2
    | ~ spl3_31
    | spl3_28 ),
    inference(avatar_split_clause,[],[f1916,f1901,f1923,f59,f1919,f54])).

fof(f59,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f1901,plain,
    ( spl3_28
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1916,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | spl3_28 ),
    inference(resolution,[],[f1903,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f1903,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f1901])).

fof(f1908,plain,
    ( ~ spl3_28
    | ~ spl3_29
    | spl3_26 ),
    inference(avatar_split_clause,[],[f1898,f1879,f1905,f1901])).

fof(f1879,plain,
    ( spl3_26
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f1898,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_26 ),
    inference(resolution,[],[f1881,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f1881,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f1879])).

fof(f1882,plain,
    ( ~ spl3_26
    | spl3_13
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f1877,f1825,f384,f1879])).

fof(f384,plain,
    ( spl3_13
  <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f1825,plain,
    ( spl3_22
  <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f1877,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_13
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f386,f1853])).

fof(f1853,plain,
    ( ! [X6] : k4_xboole_0(k1_tops_1(sK0,sK1),X6) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X6)
    | ~ spl3_22 ),
    inference(resolution,[],[f1826,f371])).

fof(f371,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X4)
      | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3) ) ),
    inference(resolution,[],[f47,f45])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1826,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f1825])).

fof(f386,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f384])).

fof(f1843,plain,
    ( ~ spl3_5
    | ~ spl3_14
    | spl3_22 ),
    inference(avatar_split_clause,[],[f1842,f1825,f1359,f77])).

fof(f1359,plain,
    ( spl3_14
  <=> sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1842,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_14
    | spl3_22 ),
    inference(superposition,[],[f1832,f1361])).

fof(f1361,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f1359])).

fof(f1832,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
    | spl3_22 ),
    inference(superposition,[],[f1829,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1829,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0))
    | spl3_22 ),
    inference(resolution,[],[f1827,f48])).

fof(f1827,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f1825])).

fof(f1362,plain,
    ( spl3_14
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f1355,f59,f54,f1359])).

fof(f1355,plain,
    ( sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(resolution,[],[f1354,f61])).

fof(f61,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f1354,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_xboole_0(X0,k1_tops_1(sK0,X0)) = X0 )
    | ~ spl3_1 ),
    inference(resolution,[],[f287,f56])).

fof(f56,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f287,plain,(
    ! [X8,X7] :
      ( ~ l1_pre_topc(X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8)))
      | k2_xboole_0(X7,k1_tops_1(X8,X7)) = X7 ) ),
    inference(forward_demodulation,[],[f286,f38])).

fof(f286,plain,(
    ! [X8,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8)))
      | ~ l1_pre_topc(X8)
      | k2_xboole_0(k1_tops_1(X8,X7),X7) = X7 ) ),
    inference(resolution,[],[f34,f41])).

fof(f387,plain,
    ( ~ spl3_13
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f372,f64,f59,f384])).

fof(f64,plain,
    ( spl3_3
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f372,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | ~ spl3_2
    | spl3_3 ),
    inference(backward_demodulation,[],[f66,f369])).

fof(f369,plain,
    ( ! [X0] : k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)
    | ~ spl3_2 ),
    inference(resolution,[],[f47,f61])).

fof(f66,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f64])).

fof(f80,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f73,f59,f77])).

fof(f73,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f46,f61])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f72,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f69])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(f67,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f31,f64])).

fof(f31,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f62,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f32,f59])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f33,f54])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:50:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (26251)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (26242)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.50  % (26235)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (26231)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (26240)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (26253)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (26238)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (26232)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (26245)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (26246)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.51  % (26249)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (26230)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (26234)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (26255)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (26233)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (26230)Refutation not found, incomplete strategy% (26230)------------------------------
% 0.21/0.52  % (26230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26230)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26230)Memory used [KB]: 10746
% 0.21/0.52  % (26230)Time elapsed: 0.098 s
% 0.21/0.52  % (26230)------------------------------
% 0.21/0.52  % (26230)------------------------------
% 0.21/0.52  % (26252)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (26236)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (26247)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (26241)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (26237)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (26239)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (26250)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (26243)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (26256)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.54  % (26236)Refutation not found, incomplete strategy% (26236)------------------------------
% 0.21/0.54  % (26236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (26236)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (26236)Memory used [KB]: 10618
% 0.21/0.54  % (26236)Time elapsed: 0.101 s
% 0.21/0.54  % (26236)------------------------------
% 0.21/0.54  % (26236)------------------------------
% 0.21/0.54  % (26248)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.55  % (26254)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.56  % (26243)Refutation not found, incomplete strategy% (26243)------------------------------
% 0.21/0.56  % (26243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26243)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (26243)Memory used [KB]: 6268
% 0.21/0.56  % (26243)Time elapsed: 0.126 s
% 0.21/0.56  % (26243)------------------------------
% 0.21/0.56  % (26243)------------------------------
% 1.76/0.60  % (26246)Refutation found. Thanks to Tanya!
% 1.76/0.60  % SZS status Theorem for theBenchmark
% 1.76/0.60  % SZS output start Proof for theBenchmark
% 1.76/0.60  fof(f2185,plain,(
% 1.76/0.60    $false),
% 1.76/0.60    inference(avatar_sat_refutation,[],[f57,f62,f67,f72,f80,f387,f1362,f1843,f1882,f1908,f1926,f1931,f1937,f1946,f2041,f2055,f2167,f2174])).
% 1.76/0.60  fof(f2174,plain,(
% 1.76/0.60    spl3_59),
% 1.76/0.60    inference(avatar_contradiction_clause,[],[f2168])).
% 1.76/0.60  fof(f2168,plain,(
% 1.76/0.60    $false | spl3_59),
% 1.76/0.60    inference(unit_resulting_resolution,[],[f36,f2166,f40])).
% 1.76/0.60  fof(f40,plain,(
% 1.76/0.60    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f22])).
% 1.76/0.60  fof(f22,plain,(
% 1.76/0.60    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.76/0.60    inference(ennf_transformation,[],[f2])).
% 1.76/0.60  fof(f2,axiom,(
% 1.76/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.76/0.60  fof(f2166,plain,(
% 1.76/0.60    ~r1_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | spl3_59),
% 1.76/0.60    inference(avatar_component_clause,[],[f2164])).
% 1.76/0.60  fof(f2164,plain,(
% 1.76/0.60    spl3_59 <=> r1_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 1.76/0.60  fof(f36,plain,(
% 1.76/0.60    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f9])).
% 1.76/0.60  fof(f9,axiom,(
% 1.76/0.60    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.76/0.60  fof(f2167,plain,(
% 1.76/0.60    ~spl3_4 | ~spl3_59 | ~spl3_1 | spl3_44),
% 1.76/0.60    inference(avatar_split_clause,[],[f2158,f2052,f54,f2164,f69])).
% 1.76/0.60  fof(f69,plain,(
% 1.76/0.60    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.76/0.60  fof(f54,plain,(
% 1.76/0.60    spl3_1 <=> l1_pre_topc(sK0)),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.76/0.60  fof(f2052,plain,(
% 1.76/0.60    spl3_44 <=> r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.76/0.60  fof(f2158,plain,(
% 1.76/0.60    ~l1_pre_topc(sK0) | ~r1_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_44),
% 1.76/0.60    inference(resolution,[],[f2054,f283])).
% 1.76/0.60  fof(f283,plain,(
% 1.76/0.60    ( ! [X2,X0,X1] : (r1_xboole_0(k1_tops_1(X1,X0),X2) | ~l1_pre_topc(X1) | ~r1_xboole_0(X0,X2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.76/0.60    inference(resolution,[],[f34,f49])).
% 1.76/0.60  fof(f49,plain,(
% 1.76/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f27])).
% 1.76/0.60  fof(f27,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.76/0.60    inference(flattening,[],[f26])).
% 1.76/0.60  fof(f26,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.76/0.60    inference(ennf_transformation,[],[f8])).
% 1.76/0.60  fof(f8,axiom,(
% 1.76/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.76/0.60  fof(f34,plain,(
% 1.76/0.60    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f19])).
% 1.76/0.60  fof(f19,plain,(
% 1.76/0.60    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.76/0.60    inference(ennf_transformation,[],[f13])).
% 1.76/0.60  fof(f13,axiom,(
% 1.76/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 1.76/0.60  fof(f2054,plain,(
% 1.76/0.60    ~r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2)) | spl3_44),
% 1.76/0.60    inference(avatar_component_clause,[],[f2052])).
% 1.76/0.60  fof(f2055,plain,(
% 1.76/0.60    ~spl3_44 | spl3_43),
% 1.76/0.60    inference(avatar_split_clause,[],[f2049,f2038,f2052])).
% 1.76/0.60  fof(f2038,plain,(
% 1.76/0.60    spl3_43 <=> r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 1.76/0.60  fof(f2049,plain,(
% 1.76/0.60    ~r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(sK1,sK2)) | spl3_43),
% 1.76/0.60    inference(resolution,[],[f2040,f40])).
% 1.76/0.60  fof(f2040,plain,(
% 1.76/0.60    ~r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) | spl3_43),
% 1.76/0.60    inference(avatar_component_clause,[],[f2038])).
% 1.76/0.60  fof(f2041,plain,(
% 1.76/0.60    ~spl3_31 | ~spl3_43 | ~spl3_1 | spl3_29),
% 1.76/0.60    inference(avatar_split_clause,[],[f2027,f1905,f54,f2038,f1923])).
% 1.76/0.60  fof(f1923,plain,(
% 1.76/0.60    spl3_31 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.76/0.60  fof(f1905,plain,(
% 1.76/0.60    spl3_29 <=> r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 1.76/0.60  fof(f2027,plain,(
% 1.76/0.60    ~l1_pre_topc(sK0) | ~r1_xboole_0(k4_xboole_0(sK1,sK2),k1_tops_1(sK0,sK2)) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_29),
% 1.76/0.60    inference(resolution,[],[f1907,f283])).
% 1.76/0.60  fof(f1907,plain,(
% 1.76/0.60    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_29),
% 1.76/0.60    inference(avatar_component_clause,[],[f1905])).
% 1.76/0.60  fof(f1946,plain,(
% 1.76/0.60    ~spl3_5 | spl3_32),
% 1.76/0.60    inference(avatar_split_clause,[],[f1940,f1934,f77])).
% 1.76/0.60  fof(f77,plain,(
% 1.76/0.60    spl3_5 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.76/0.60  fof(f1934,plain,(
% 1.76/0.60    spl3_32 <=> r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.76/0.60  fof(f1940,plain,(
% 1.76/0.60    ~r1_tarski(sK1,u1_struct_0(sK0)) | spl3_32),
% 1.76/0.60    inference(superposition,[],[f1938,f87])).
% 1.76/0.60  fof(f87,plain,(
% 1.76/0.60    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),X1) = X1) )),
% 1.76/0.60    inference(resolution,[],[f41,f37])).
% 1.76/0.60  fof(f37,plain,(
% 1.76/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f6])).
% 1.76/0.60  fof(f6,axiom,(
% 1.76/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.76/0.60  fof(f41,plain,(
% 1.76/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.76/0.60    inference(cnf_transformation,[],[f23])).
% 1.76/0.60  fof(f23,plain,(
% 1.76/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.76/0.60    inference(ennf_transformation,[],[f5])).
% 1.76/0.60  fof(f5,axiom,(
% 1.76/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.76/0.60  fof(f1938,plain,(
% 1.76/0.60    ( ! [X0] : (~r1_tarski(k2_xboole_0(k4_xboole_0(sK1,sK2),X0),u1_struct_0(sK0))) ) | spl3_32),
% 1.76/0.60    inference(resolution,[],[f1936,f48])).
% 1.76/0.60  fof(f48,plain,(
% 1.76/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f25])).
% 1.76/0.60  fof(f25,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.76/0.60    inference(ennf_transformation,[],[f4])).
% 1.76/0.60  fof(f4,axiom,(
% 1.76/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.76/0.60  fof(f1936,plain,(
% 1.76/0.60    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_32),
% 1.76/0.60    inference(avatar_component_clause,[],[f1934])).
% 1.76/0.60  fof(f1937,plain,(
% 1.76/0.60    ~spl3_32 | spl3_31),
% 1.76/0.60    inference(avatar_split_clause,[],[f1932,f1923,f1934])).
% 1.76/0.60  fof(f1932,plain,(
% 1.76/0.60    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) | spl3_31),
% 1.76/0.60    inference(resolution,[],[f1925,f45])).
% 1.76/0.60  fof(f45,plain,(
% 1.76/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f12])).
% 1.76/0.60  fof(f12,axiom,(
% 1.76/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.76/0.60  fof(f1925,plain,(
% 1.76/0.60    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_31),
% 1.76/0.60    inference(avatar_component_clause,[],[f1923])).
% 1.76/0.60  fof(f1931,plain,(
% 1.76/0.60    spl3_30),
% 1.76/0.60    inference(avatar_contradiction_clause,[],[f1927])).
% 1.76/0.60  fof(f1927,plain,(
% 1.76/0.60    $false | spl3_30),
% 1.76/0.60    inference(unit_resulting_resolution,[],[f37,f1921])).
% 1.76/0.60  fof(f1921,plain,(
% 1.76/0.60    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | spl3_30),
% 1.76/0.60    inference(avatar_component_clause,[],[f1919])).
% 1.76/0.60  fof(f1919,plain,(
% 1.76/0.60    spl3_30 <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1)),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.76/0.60  fof(f1926,plain,(
% 1.76/0.60    ~spl3_1 | ~spl3_30 | ~spl3_2 | ~spl3_31 | spl3_28),
% 1.76/0.60    inference(avatar_split_clause,[],[f1916,f1901,f1923,f59,f1919,f54])).
% 1.76/0.60  fof(f59,plain,(
% 1.76/0.60    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.76/0.60  fof(f1901,plain,(
% 1.76/0.60    spl3_28 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.76/0.60  fof(f1916,plain,(
% 1.76/0.60    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0) | spl3_28),
% 1.76/0.60    inference(resolution,[],[f1903,f35])).
% 1.76/0.60  fof(f35,plain,(
% 1.76/0.60    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f21])).
% 1.76/0.60  fof(f21,plain,(
% 1.76/0.60    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.76/0.60    inference(flattening,[],[f20])).
% 1.76/0.60  fof(f20,plain,(
% 1.76/0.60    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.76/0.60    inference(ennf_transformation,[],[f14])).
% 1.76/0.60  fof(f14,axiom,(
% 1.76/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 1.76/0.60  fof(f1903,plain,(
% 1.76/0.60    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_28),
% 1.76/0.60    inference(avatar_component_clause,[],[f1901])).
% 1.76/0.60  fof(f1908,plain,(
% 1.76/0.60    ~spl3_28 | ~spl3_29 | spl3_26),
% 1.76/0.60    inference(avatar_split_clause,[],[f1898,f1879,f1905,f1901])).
% 1.76/0.60  fof(f1879,plain,(
% 1.76/0.60    spl3_26 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.76/0.60  fof(f1898,plain,(
% 1.76/0.60    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_26),
% 1.76/0.60    inference(resolution,[],[f1881,f50])).
% 1.76/0.60  fof(f50,plain,(
% 1.76/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f29])).
% 1.76/0.60  fof(f29,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 1.76/0.60    inference(flattening,[],[f28])).
% 1.76/0.60  fof(f28,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.76/0.60    inference(ennf_transformation,[],[f10])).
% 1.76/0.60  fof(f10,axiom,(
% 1.76/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 1.76/0.60  fof(f1881,plain,(
% 1.76/0.60    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl3_26),
% 1.76/0.60    inference(avatar_component_clause,[],[f1879])).
% 1.76/0.60  fof(f1882,plain,(
% 1.76/0.60    ~spl3_26 | spl3_13 | ~spl3_22),
% 1.76/0.60    inference(avatar_split_clause,[],[f1877,f1825,f384,f1879])).
% 1.76/0.60  fof(f384,plain,(
% 1.76/0.60    spl3_13 <=> r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.76/0.60  fof(f1825,plain,(
% 1.76/0.60    spl3_22 <=> r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.76/0.60  fof(f1877,plain,(
% 1.76/0.60    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | (spl3_13 | ~spl3_22)),
% 1.76/0.60    inference(backward_demodulation,[],[f386,f1853])).
% 1.76/0.60  fof(f1853,plain,(
% 1.76/0.60    ( ! [X6] : (k4_xboole_0(k1_tops_1(sK0,sK1),X6) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X6)) ) | ~spl3_22),
% 1.76/0.60    inference(resolution,[],[f1826,f371])).
% 1.76/0.60  fof(f371,plain,(
% 1.76/0.60    ( ! [X4,X2,X3] : (~r1_tarski(X2,X4) | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3)) )),
% 1.76/0.60    inference(resolution,[],[f47,f45])).
% 1.76/0.60  fof(f47,plain,(
% 1.76/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f24])).
% 1.76/0.60  fof(f24,plain,(
% 1.76/0.60    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.76/0.60    inference(ennf_transformation,[],[f11])).
% 1.76/0.60  fof(f11,axiom,(
% 1.76/0.60    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.76/0.60  fof(f1826,plain,(
% 1.76/0.60    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~spl3_22),
% 1.76/0.60    inference(avatar_component_clause,[],[f1825])).
% 1.76/0.60  fof(f386,plain,(
% 1.76/0.60    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl3_13),
% 1.76/0.60    inference(avatar_component_clause,[],[f384])).
% 1.76/0.60  fof(f1843,plain,(
% 1.76/0.60    ~spl3_5 | ~spl3_14 | spl3_22),
% 1.76/0.60    inference(avatar_split_clause,[],[f1842,f1825,f1359,f77])).
% 1.76/0.60  fof(f1359,plain,(
% 1.76/0.60    spl3_14 <=> sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.76/0.60  fof(f1842,plain,(
% 1.76/0.60    ~r1_tarski(sK1,u1_struct_0(sK0)) | (~spl3_14 | spl3_22)),
% 1.76/0.60    inference(superposition,[],[f1832,f1361])).
% 1.76/0.60  fof(f1361,plain,(
% 1.76/0.60    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | ~spl3_14),
% 1.76/0.60    inference(avatar_component_clause,[],[f1359])).
% 1.76/0.60  fof(f1832,plain,(
% 1.76/0.60    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))) ) | spl3_22),
% 1.76/0.60    inference(superposition,[],[f1829,f38])).
% 1.76/0.60  fof(f38,plain,(
% 1.76/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f1])).
% 1.76/0.60  fof(f1,axiom,(
% 1.76/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.76/0.60  fof(f1829,plain,(
% 1.76/0.60    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_tops_1(sK0,sK1),X0),u1_struct_0(sK0))) ) | spl3_22),
% 1.76/0.60    inference(resolution,[],[f1827,f48])).
% 1.76/0.60  fof(f1827,plain,(
% 1.76/0.60    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_22),
% 1.76/0.60    inference(avatar_component_clause,[],[f1825])).
% 1.76/0.60  fof(f1362,plain,(
% 1.76/0.60    spl3_14 | ~spl3_1 | ~spl3_2),
% 1.76/0.60    inference(avatar_split_clause,[],[f1355,f59,f54,f1359])).
% 1.76/0.60  fof(f1355,plain,(
% 1.76/0.60    sK1 = k2_xboole_0(sK1,k1_tops_1(sK0,sK1)) | (~spl3_1 | ~spl3_2)),
% 1.76/0.60    inference(resolution,[],[f1354,f61])).
% 1.76/0.60  fof(f61,plain,(
% 1.76/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 1.76/0.60    inference(avatar_component_clause,[],[f59])).
% 1.76/0.60  fof(f1354,plain,(
% 1.76/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_xboole_0(X0,k1_tops_1(sK0,X0)) = X0) ) | ~spl3_1),
% 1.76/0.60    inference(resolution,[],[f287,f56])).
% 1.76/0.60  fof(f56,plain,(
% 1.76/0.60    l1_pre_topc(sK0) | ~spl3_1),
% 1.76/0.60    inference(avatar_component_clause,[],[f54])).
% 1.76/0.60  fof(f287,plain,(
% 1.76/0.60    ( ! [X8,X7] : (~l1_pre_topc(X8) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8))) | k2_xboole_0(X7,k1_tops_1(X8,X7)) = X7) )),
% 1.76/0.60    inference(forward_demodulation,[],[f286,f38])).
% 1.76/0.60  fof(f286,plain,(
% 1.76/0.60    ( ! [X8,X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X8))) | ~l1_pre_topc(X8) | k2_xboole_0(k1_tops_1(X8,X7),X7) = X7) )),
% 1.76/0.60    inference(resolution,[],[f34,f41])).
% 1.76/0.60  fof(f387,plain,(
% 1.76/0.60    ~spl3_13 | ~spl3_2 | spl3_3),
% 1.76/0.60    inference(avatar_split_clause,[],[f372,f64,f59,f384])).
% 1.76/0.60  fof(f64,plain,(
% 1.76/0.60    spl3_3 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.76/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.76/0.60  fof(f372,plain,(
% 1.76/0.60    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | (~spl3_2 | spl3_3)),
% 1.76/0.60    inference(backward_demodulation,[],[f66,f369])).
% 1.76/0.60  fof(f369,plain,(
% 1.76/0.60    ( ! [X0] : (k4_xboole_0(sK1,X0) = k7_subset_1(u1_struct_0(sK0),sK1,X0)) ) | ~spl3_2),
% 1.76/0.60    inference(resolution,[],[f47,f61])).
% 1.76/0.60  fof(f66,plain,(
% 1.76/0.60    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) | spl3_3),
% 1.76/0.60    inference(avatar_component_clause,[],[f64])).
% 1.76/0.60  fof(f80,plain,(
% 1.76/0.60    spl3_5 | ~spl3_2),
% 1.76/0.60    inference(avatar_split_clause,[],[f73,f59,f77])).
% 1.76/0.60  fof(f73,plain,(
% 1.76/0.60    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_2),
% 1.76/0.60    inference(resolution,[],[f46,f61])).
% 1.76/0.60  fof(f46,plain,(
% 1.76/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.76/0.60    inference(cnf_transformation,[],[f12])).
% 1.76/0.60  fof(f72,plain,(
% 1.76/0.60    spl3_4),
% 1.76/0.60    inference(avatar_split_clause,[],[f30,f69])).
% 1.76/0.60  fof(f30,plain,(
% 1.76/0.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.76/0.60    inference(cnf_transformation,[],[f18])).
% 1.76/0.60  fof(f18,plain,(
% 1.76/0.60    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.76/0.60    inference(ennf_transformation,[],[f17])).
% 1.76/0.60  fof(f17,plain,(
% 1.76/0.60    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.76/0.60    inference(pure_predicate_removal,[],[f16])).
% 1.76/0.60  fof(f16,negated_conjecture,(
% 1.76/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.76/0.60    inference(negated_conjecture,[],[f15])).
% 1.76/0.60  fof(f15,conjecture,(
% 1.76/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).
% 1.76/0.60  fof(f67,plain,(
% 1.76/0.60    ~spl3_3),
% 1.76/0.60    inference(avatar_split_clause,[],[f31,f64])).
% 1.76/0.60  fof(f31,plain,(
% 1.76/0.60    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 1.76/0.60    inference(cnf_transformation,[],[f18])).
% 1.76/0.60  fof(f62,plain,(
% 1.76/0.60    spl3_2),
% 1.76/0.60    inference(avatar_split_clause,[],[f32,f59])).
% 1.76/0.60  fof(f32,plain,(
% 1.76/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.76/0.60    inference(cnf_transformation,[],[f18])).
% 1.76/0.60  fof(f57,plain,(
% 1.76/0.60    spl3_1),
% 1.76/0.60    inference(avatar_split_clause,[],[f33,f54])).
% 1.76/0.60  fof(f33,plain,(
% 1.76/0.60    l1_pre_topc(sK0)),
% 1.76/0.60    inference(cnf_transformation,[],[f18])).
% 1.76/0.60  % SZS output end Proof for theBenchmark
% 1.76/0.60  % (26246)------------------------------
% 1.76/0.60  % (26246)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (26246)Termination reason: Refutation
% 1.76/0.60  
% 1.76/0.60  % (26246)Memory used [KB]: 7419
% 1.76/0.60  % (26246)Time elapsed: 0.190 s
% 1.76/0.60  % (26246)------------------------------
% 1.76/0.60  % (26246)------------------------------
% 1.76/0.60  % (26223)Success in time 0.234 s
%------------------------------------------------------------------------------
