%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 197 expanded)
%              Number of leaves         :   26 (  73 expanded)
%              Depth                    :   12
%              Number of atoms          :  244 ( 397 expanded)
%              Number of equality atoms :   56 ( 120 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f85,f90,f107,f126,f152,f161])).

fof(f161,plain,
    ( ~ spl1_2
    | ~ spl1_7
    | spl1_8 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_7
    | spl1_8 ),
    inference(subsumption_resolution,[],[f159,f151])).

fof(f151,plain,
    ( u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))
    | spl1_8 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl1_8
  <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f159,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl1_2
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f158,f62])).

fof(f62,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f43,f61])).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f46,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f46,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f158,plain,
    ( k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl1_2
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f157,f134])).

fof(f134,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_7 ),
    inference(unit_resulting_resolution,[],[f73,f44,f125,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f125,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl1_7
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f44,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f73,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f157,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl1_2 ),
    inference(backward_demodulation,[],[f132,f153])).

fof(f153,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f92,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f92,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(unit_resulting_resolution,[],[f64,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f64,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f63,f62])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f45,f61])).

fof(f45,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f132,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl1_2 ),
    inference(forward_demodulation,[],[f130,f112])).

fof(f112,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f64,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f130,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f73,f64,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f152,plain,
    ( ~ spl1_8
    | ~ spl1_3
    | spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f146,f104,f87,f82,f76,f149])).

fof(f76,plain,
    ( spl1_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f82,plain,
    ( spl1_4
  <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f87,plain,
    ( spl1_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f104,plain,
    ( spl1_6
  <=> v1_xboole_0(k1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f146,plain,
    ( u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl1_3
    | spl1_4
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(backward_demodulation,[],[f84,f145])).

fof(f145,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f144,f62])).

fof(f144,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(backward_demodulation,[],[f100,f140])).

fof(f140,plain,
    ( k1_xboole_0 = k1_struct_0(sK0)
    | ~ spl1_3
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f78,f106,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f106,plain,
    ( v1_xboole_0(k1_struct_0(sK0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f78,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f100,plain,
    ( k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f89,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).

fof(f89,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f84,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    | spl1_4 ),
    inference(avatar_component_clause,[],[f82])).

fof(f126,plain,
    ( spl1_7
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(avatar_split_clause,[],[f118,f76,f71,f66,f123])).

fof(f66,plain,
    ( spl1_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f118,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_3 ),
    inference(unit_resulting_resolution,[],[f68,f73,f78,f44,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
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
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f68,plain,
    ( v2_pre_topc(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f107,plain,
    ( spl1_6
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f96,f87,f104])).

fof(f96,plain,
    ( v1_xboole_0(k1_struct_0(sK0))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f89,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_struct_0(X0))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => v1_xboole_0(k1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).

fof(f90,plain,
    ( spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f80,f71,f87])).

fof(f80,plain,
    ( l1_struct_0(sK0)
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f73,f49])).

fof(f49,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f85,plain,(
    ~ spl1_4 ),
    inference(avatar_split_clause,[],[f40,f82])).

fof(f40,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(f79,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f41,f76])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f74,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f39,f71])).

fof(f39,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f69,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f38,f66])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:00:10 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.42  % (9498)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.42  % (9498)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f162,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f69,f74,f79,f85,f90,f107,f126,f152,f161])).
% 0.21/0.42  fof(f161,plain,(
% 0.21/0.42    ~spl1_2 | ~spl1_7 | spl1_8),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f160])).
% 0.21/0.42  fof(f160,plain,(
% 0.21/0.42    $false | (~spl1_2 | ~spl1_7 | spl1_8)),
% 0.21/0.42    inference(subsumption_resolution,[],[f159,f151])).
% 0.21/0.42  fof(f151,plain,(
% 0.21/0.42    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) | spl1_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f149])).
% 0.21/0.42  fof(f149,plain,(
% 0.21/0.42    spl1_8 <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.42  fof(f159,plain,(
% 0.21/0.42    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) | (~spl1_2 | ~spl1_7)),
% 0.21/0.42    inference(forward_demodulation,[],[f158,f62])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.21/0.42    inference(definition_unfolding,[],[f43,f61])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f46,f42])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.42  fof(f158,plain,(
% 0.21/0.42    k3_subset_1(u1_struct_0(sK0),k1_xboole_0) = k1_tops_1(sK0,u1_struct_0(sK0)) | (~spl1_2 | ~spl1_7)),
% 0.21/0.42    inference(forward_demodulation,[],[f157,f134])).
% 0.21/0.42  fof(f134,plain,(
% 0.21/0.42    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | (~spl1_2 | ~spl1_7)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f73,f44,f125,f51])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.42    inference(cnf_transformation,[],[f27])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(flattening,[],[f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.42  fof(f125,plain,(
% 0.21/0.42    v4_pre_topc(k1_xboole_0,sK0) | ~spl1_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f123])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    spl1_7 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,axiom,(
% 0.21/0.42    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.42  fof(f73,plain,(
% 0.21/0.42    l1_pre_topc(sK0) | ~spl1_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f71])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    spl1_2 <=> l1_pre_topc(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.42  fof(f157,plain,(
% 0.21/0.42    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) | ~spl1_2),
% 0.21/0.42    inference(backward_demodulation,[],[f132,f153])).
% 0.21/0.42  fof(f153,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f92,f58])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.42    inference(nnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f64,f55])).
% 0.21/0.42  fof(f55,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f36])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.42    inference(nnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(forward_demodulation,[],[f63,f62])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(definition_unfolding,[],[f45,f61])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl1_2),
% 0.21/0.42    inference(forward_demodulation,[],[f130,f112])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f64,f54])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f30])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | ~spl1_2),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f73,f64,f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.42  fof(f152,plain,(
% 0.21/0.42    ~spl1_8 | ~spl1_3 | spl1_4 | ~spl1_5 | ~spl1_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f146,f104,f87,f82,f76,f149])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl1_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    spl1_4 <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    spl1_5 <=> l1_struct_0(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    spl1_6 <=> v1_xboole_0(k1_struct_0(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.42  fof(f146,plain,(
% 0.21/0.42    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) | (~spl1_3 | spl1_4 | ~spl1_5 | ~spl1_6)),
% 0.21/0.42    inference(backward_demodulation,[],[f84,f145])).
% 0.21/0.42  fof(f145,plain,(
% 0.21/0.42    k2_struct_0(sK0) = u1_struct_0(sK0) | (~spl1_3 | ~spl1_5 | ~spl1_6)),
% 0.21/0.42    inference(forward_demodulation,[],[f144,f62])).
% 0.21/0.42  fof(f144,plain,(
% 0.21/0.42    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | (~spl1_3 | ~spl1_5 | ~spl1_6)),
% 0.21/0.42    inference(backward_demodulation,[],[f100,f140])).
% 0.21/0.42  fof(f140,plain,(
% 0.21/0.42    k1_xboole_0 = k1_struct_0(sK0) | (~spl1_3 | ~spl1_6)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f78,f106,f59])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    v1_xboole_0(k1_struct_0(sK0)) | ~spl1_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f104])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0) | ~spl1_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f76])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    k2_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_struct_0(sK0)) | ~spl1_5),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f89,f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ! [X0] : (k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f15])).
% 0.21/0.42  fof(f15,axiom,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = k3_subset_1(u1_struct_0(X0),k1_struct_0(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_pre_topc)).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    l1_struct_0(sK0) | ~spl1_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f87])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) | spl1_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f82])).
% 0.21/0.42  fof(f126,plain,(
% 0.21/0.42    spl1_7 | ~spl1_1 | ~spl1_2 | ~spl1_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f118,f76,f71,f66,f123])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl1_1 <=> v2_pre_topc(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    v4_pre_topc(k1_xboole_0,sK0) | (~spl1_1 | ~spl1_2 | ~spl1_3)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f68,f73,f78,f44,f53])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f29])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.42    inference(flattening,[],[f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,axiom,(
% 0.21/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    v2_pre_topc(sK0) | ~spl1_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    spl1_6 | ~spl1_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f96,f87,f104])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    v1_xboole_0(k1_struct_0(sK0)) | ~spl1_5),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f89,f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(k1_struct_0(X0)) | ~l1_struct_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,axiom,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) => v1_xboole_0(k1_struct_0(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_struct_0)).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    spl1_5 | ~spl1_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f80,f71,f87])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    l1_struct_0(sK0) | ~spl1_2),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f73,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,axiom,(
% 0.21/0.42    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    ~spl1_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f40,f82])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.42    inference(flattening,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f19])).
% 0.21/0.42  fof(f19,negated_conjecture,(
% 0.21/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f18])).
% 0.21/0.42  fof(f18,conjecture,(
% 0.21/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    spl1_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f41,f76])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl1_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f39,f71])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    l1_pre_topc(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f35])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    spl1_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f38,f66])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    v2_pre_topc(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f35])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (9498)------------------------------
% 0.21/0.42  % (9498)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (9498)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (9498)Memory used [KB]: 10618
% 0.21/0.42  % (9498)Time elapsed: 0.008 s
% 0.21/0.42  % (9498)------------------------------
% 0.21/0.42  % (9498)------------------------------
% 0.21/0.43  % (9482)Success in time 0.071 s
%------------------------------------------------------------------------------
