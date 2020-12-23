%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1270+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:15 EST 2020

% Result     : Theorem 14.18s
% Output     : Refutation 14.18s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 375 expanded)
%              Number of leaves         :   44 ( 137 expanded)
%              Depth                    :   17
%              Number of atoms          :  555 (1067 expanded)
%              Number of equality atoms :   75 ( 133 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f22969,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3670,f3680,f3699,f3705,f3757,f3998,f4121,f4178,f5234,f5577,f10345,f10383,f10611,f10758,f10806,f13918,f16272,f22948])).

fof(f22948,plain,
    ( ~ spl106_1
    | spl106_7
    | ~ spl106_15
    | ~ spl106_29
    | ~ spl106_65
    | ~ spl106_91
    | ~ spl106_129
    | ~ spl106_157
    | ~ spl106_182 ),
    inference(avatar_contradiction_clause,[],[f22947])).

fof(f22947,plain,
    ( $false
    | ~ spl106_1
    | spl106_7
    | ~ spl106_15
    | ~ spl106_29
    | ~ spl106_65
    | ~ spl106_91
    | ~ spl106_129
    | ~ spl106_157
    | ~ spl106_182 ),
    inference(subsumption_resolution,[],[f22940,f3756])).

fof(f3756,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl106_15 ),
    inference(avatar_component_clause,[],[f3754])).

fof(f3754,plain,
    ( spl106_15
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_15])])).

fof(f22940,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl106_1
    | spl106_7
    | ~ spl106_29
    | ~ spl106_65
    | ~ spl106_91
    | ~ spl106_129
    | ~ spl106_157
    | ~ spl106_182 ),
    inference(backward_demodulation,[],[f11510,f22939])).

fof(f22939,plain,
    ( u1_struct_0(sK0) = k2_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl106_1
    | ~ spl106_29
    | ~ spl106_65
    | ~ spl106_91
    | ~ spl106_157
    | ~ spl106_182 ),
    inference(backward_demodulation,[],[f22520,f22938])).

fof(f22938,plain,
    ( u1_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl106_1
    | ~ spl106_65
    | ~ spl106_91
    | ~ spl106_157
    | ~ spl106_182 ),
    inference(forward_demodulation,[],[f22937,f22674])).

fof(f22674,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl106_1
    | ~ spl106_91
    | ~ spl106_157
    | ~ spl106_182 ),
    inference(forward_demodulation,[],[f22249,f13949])).

fof(f13949,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl106_157 ),
    inference(forward_demodulation,[],[f13948,f6946])).

fof(f6946,plain,(
    ! [X0] : k4_subset_1(X0,k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f6231,f6944])).

fof(f6944,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f6943,f6401])).

fof(f6401,plain,(
    ! [X0] : k4_subset_1(X0,X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f6240,f3310])).

fof(f3310,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f6240,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f3733,f3107,f3032])).

fof(f3032,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2294])).

fof(f2294,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f2293])).

fof(f2293,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f491])).

fof(f491,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f3107,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f3733,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f3551,f2896])).

fof(f2896,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2654])).

fof(f2654,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f609])).

fof(f609,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f3551,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f2905])).

fof(f2905,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2664])).

fof(f2664,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f2663])).

fof(f2663,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f6943,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f6830,f6231])).

fof(f6830,plain,(
    ! [X0] : k4_subset_1(X0,X0,k1_xboole_0) = k4_subset_1(X0,k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f3733,f3107,f3031])).

fof(f3031,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f2292])).

fof(f2292,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f2291])).

fof(f2291,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f451])).

fof(f451,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

fof(f6231,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k4_subset_1(X0,k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f3107,f3733,f3032])).

fof(f13948,plain,
    ( k4_subset_1(u1_struct_0(sK0),k1_xboole_0,u1_struct_0(sK0)) = k2_struct_0(sK0)
    | ~ spl106_157 ),
    inference(forward_demodulation,[],[f13933,f5543])).

fof(f5543,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f5492,f3460])).

fof(f3460,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f5492,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f3107,f3131])).

fof(f3131,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2381])).

fof(f2381,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f13933,plain,
    ( k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_subset_1(u1_struct_0(sK0),k1_xboole_0))
    | ~ spl106_157 ),
    inference(unit_resulting_resolution,[],[f3107,f13917,f3043])).

fof(f3043,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f2308])).

fof(f2308,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1823])).

fof(f1823,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_struct_0(X0) = k4_subset_1(u1_struct_0(X0),X1,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_pre_topc)).

fof(f13917,plain,
    ( l1_struct_0(sK0)
    | ~ spl106_157 ),
    inference(avatar_component_clause,[],[f13915])).

fof(f13915,plain,
    ( spl106_157
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_157])])).

fof(f22249,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl106_1
    | ~ spl106_91
    | ~ spl106_182 ),
    inference(unit_resulting_resolution,[],[f3669,f7901,f16271,f3227])).

fof(f3227,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2811])).

fof(f2811,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | k2_pre_topc(X0,X1) != k2_struct_0(X0) )
            & ( k2_pre_topc(X0,X1) = k2_struct_0(X0)
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2461])).

fof(f2461,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2090])).

fof(f2090,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_pre_topc(X0,X1) = k2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f16271,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl106_182 ),
    inference(avatar_component_clause,[],[f16269])).

fof(f16269,plain,
    ( spl106_182
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_182])])).

fof(f7901,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl106_91 ),
    inference(avatar_component_clause,[],[f7900])).

fof(f7900,plain,
    ( spl106_91
  <=> v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_91])])).

fof(f3669,plain,
    ( l1_pre_topc(sK0)
    | ~ spl106_1 ),
    inference(avatar_component_clause,[],[f3667])).

fof(f3667,plain,
    ( spl106_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_1])])).

fof(f22937,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl106_1
    | ~ spl106_65
    | ~ spl106_182 ),
    inference(forward_demodulation,[],[f22174,f5576])).

fof(f5576,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl106_65 ),
    inference(avatar_component_clause,[],[f5574])).

fof(f5574,plain,
    ( spl106_65
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_65])])).

fof(f22174,plain,
    ( k2_pre_topc(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1)))
    | ~ spl106_1
    | ~ spl106_182 ),
    inference(unit_resulting_resolution,[],[f3669,f16271,f2930])).

fof(f2930,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f2209])).

fof(f2209,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2148])).

fof(f2148,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f22520,plain,
    ( k2_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl106_29
    | ~ spl106_182 ),
    inference(forward_demodulation,[],[f22320,f3305])).

fof(f3305,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f22320,plain,
    ( k2_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k4_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl106_29
    | ~ spl106_182 ),
    inference(unit_resulting_resolution,[],[f3997,f16271,f3032])).

fof(f3997,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl106_29 ),
    inference(avatar_component_clause,[],[f3995])).

fof(f3995,plain,
    ( spl106_29
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_29])])).

fof(f11510,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(k2_tops_1(sK0,sK1),k4_xboole_0(u1_struct_0(sK0),sK1)))
    | spl106_7
    | ~ spl106_129 ),
    inference(unit_resulting_resolution,[],[f3697,f10805,f3149])).

fof(f3149,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2401])).

fof(f2401,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f2400])).

fof(f2400,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f141])).

fof(f141,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f10805,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl106_129 ),
    inference(avatar_component_clause,[],[f10803])).

fof(f10803,plain,
    ( spl106_129
  <=> r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_129])])).

fof(f3697,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | spl106_7 ),
    inference(avatar_component_clause,[],[f3696])).

fof(f3696,plain,
    ( spl106_7
  <=> r1_tarski(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_7])])).

fof(f16272,plain,
    ( spl106_182
    | ~ spl106_3 ),
    inference(avatar_split_clause,[],[f5527,f3677,f16269])).

fof(f3677,plain,
    ( spl106_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_3])])).

fof(f5527,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl106_3 ),
    inference(backward_demodulation,[],[f5313,f5496])).

fof(f5496,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl106_3 ),
    inference(unit_resulting_resolution,[],[f3679,f3131])).

fof(f3679,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl106_3 ),
    inference(avatar_component_clause,[],[f3677])).

fof(f5313,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl106_3 ),
    inference(unit_resulting_resolution,[],[f3679,f3132])).

fof(f3132,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2382])).

fof(f2382,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f13918,plain,
    ( spl106_157
    | ~ spl106_1 ),
    inference(avatar_split_clause,[],[f13912,f3667,f13915])).

fof(f13912,plain,
    ( l1_struct_0(sK0)
    | ~ spl106_1 ),
    inference(unit_resulting_resolution,[],[f3669,f3368])).

fof(f3368,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2552])).

fof(f2552,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1782])).

fof(f1782,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f10806,plain,
    ( spl106_129
    | ~ spl106_3 ),
    inference(avatar_split_clause,[],[f6523,f3677,f10803])).

fof(f6523,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl106_3 ),
    inference(forward_demodulation,[],[f6511,f5496])).

fof(f6511,plain,
    ( r1_xboole_0(sK1,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl106_3 ),
    inference(unit_resulting_resolution,[],[f3551,f3679,f3679,f3112])).

fof(f3112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2758])).

fof(f2758,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
              | ~ r1_tarski(X1,X2) )
            & ( r1_tarski(X1,X2)
              | ~ r1_xboole_0(X1,k3_subset_1(X0,X2)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f2363])).

fof(f2363,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f517])).

fof(f517,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f10758,plain,
    ( spl106_91
    | ~ spl106_1
    | ~ spl106_3
    | ~ spl106_6 ),
    inference(avatar_split_clause,[],[f10614,f3692,f3677,f3667,f7900])).

fof(f3692,plain,
    ( spl106_6
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_6])])).

fof(f10614,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl106_1
    | ~ spl106_3
    | ~ spl106_6 ),
    inference(forward_demodulation,[],[f10612,f5496])).

fof(f10612,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl106_1
    | ~ spl106_3
    | ~ spl106_6 ),
    inference(unit_resulting_resolution,[],[f3669,f3679,f3694,f2953])).

fof(f2953,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2684])).

fof(f2684,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2222])).

fof(f2222,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2091])).

fof(f2091,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f3694,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl106_6 ),
    inference(avatar_component_clause,[],[f3692])).

fof(f10611,plain,
    ( spl106_6
    | ~ spl106_1
    | ~ spl106_3
    | ~ spl106_25 ),
    inference(avatar_split_clause,[],[f5120,f3904,f3677,f3667,f3692])).

fof(f3904,plain,
    ( spl106_25
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_25])])).

fof(f5120,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl106_1
    | ~ spl106_3
    | ~ spl106_25 ),
    inference(unit_resulting_resolution,[],[f3669,f3679,f3905,f2956])).

fof(f2956,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2685])).

fof(f2685,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2223])).

fof(f2223,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2165])).

fof(f2165,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f3905,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl106_25 ),
    inference(avatar_component_clause,[],[f3904])).

fof(f10383,plain,
    ( ~ spl106_7
    | ~ spl106_30
    | spl106_34
    | ~ spl106_124 ),
    inference(avatar_contradiction_clause,[],[f10382])).

fof(f10382,plain,
    ( $false
    | ~ spl106_7
    | ~ spl106_30
    | spl106_34
    | ~ spl106_124 ),
    inference(subsumption_resolution,[],[f10350,f4435])).

fof(f4435,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl106_30
    | spl106_34 ),
    inference(unit_resulting_resolution,[],[f4120,f4011,f3168])).

fof(f3168,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f2420])).

fof(f2420,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f2419])).

fof(f2419,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f135])).

fof(f135,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f4011,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl106_30 ),
    inference(avatar_component_clause,[],[f4009])).

fof(f4009,plain,
    ( spl106_30
  <=> r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_30])])).

fof(f4120,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK1))
    | spl106_34 ),
    inference(avatar_component_clause,[],[f4118])).

fof(f4118,plain,
    ( spl106_34
  <=> v1_xboole_0(k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_34])])).

fof(f10350,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl106_7
    | ~ spl106_124 ),
    inference(unit_resulting_resolution,[],[f3698,f10344,f2893])).

fof(f2893,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f2178])).

fof(f2178,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f2177])).

fof(f2177,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f77])).

fof(f77,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f10344,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl106_124 ),
    inference(avatar_component_clause,[],[f10342])).

fof(f10342,plain,
    ( spl106_124
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_124])])).

fof(f3698,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ spl106_7 ),
    inference(avatar_component_clause,[],[f3696])).

fof(f10345,plain,
    ( spl106_124
    | ~ spl106_1
    | ~ spl106_3 ),
    inference(avatar_split_clause,[],[f5851,f3677,f3667,f10342])).

fof(f5851,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl106_1
    | ~ spl106_3 ),
    inference(unit_resulting_resolution,[],[f3669,f3679,f3088])).

fof(f3088,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f2345])).

fof(f2345,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2133])).

fof(f2133,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f5577,plain,
    ( spl106_65
    | ~ spl106_3
    | ~ spl106_38 ),
    inference(avatar_split_clause,[],[f5522,f4175,f3677,f5574])).

fof(f4175,plain,
    ( spl106_38
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl106_38])])).

fof(f5522,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k4_xboole_0(u1_struct_0(sK0),sK1))
    | ~ spl106_3
    | ~ spl106_38 ),
    inference(backward_demodulation,[],[f4177,f5496])).

fof(f4177,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl106_38 ),
    inference(avatar_component_clause,[],[f4175])).

fof(f5234,plain,
    ( spl106_30
    | ~ spl106_1
    | ~ spl106_3 ),
    inference(avatar_split_clause,[],[f5064,f3677,f3667,f4009])).

fof(f5064,plain,
    ( r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl106_1
    | ~ spl106_3 ),
    inference(unit_resulting_resolution,[],[f3669,f3679,f2935])).

fof(f2935,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2214])).

fof(f2214,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2156])).

fof(f2156,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

fof(f4178,plain,
    ( spl106_38
    | ~ spl106_1
    | ~ spl106_3 ),
    inference(avatar_split_clause,[],[f3793,f3677,f3667,f4175])).

fof(f3793,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl106_1
    | ~ spl106_3 ),
    inference(unit_resulting_resolution,[],[f3669,f3679,f2931])).

fof(f2931,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f2210])).

fof(f2210,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2146])).

fof(f2146,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f4121,plain,
    ( ~ spl106_34
    | spl106_25 ),
    inference(avatar_split_clause,[],[f4045,f3904,f4118])).

fof(f4045,plain,
    ( ~ v1_xboole_0(k1_tops_1(sK0,sK1))
    | spl106_25 ),
    inference(unit_resulting_resolution,[],[f3906,f3252])).

fof(f3252,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f2476])).

fof(f2476,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f136])).

fof(f136,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f3906,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl106_25 ),
    inference(avatar_component_clause,[],[f3904])).

fof(f3998,plain,
    ( spl106_29
    | ~ spl106_1
    | ~ spl106_3 ),
    inference(avatar_split_clause,[],[f3760,f3677,f3667,f3995])).

fof(f3760,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl106_1
    | ~ spl106_3 ),
    inference(unit_resulting_resolution,[],[f3669,f3679,f2913])).

fof(f2913,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2187])).

fof(f2187,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2186])).

fof(f2186,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2093])).

fof(f2093,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f3757,plain,
    ( spl106_15
    | ~ spl106_3 ),
    inference(avatar_split_clause,[],[f3725,f3677,f3754])).

fof(f3725,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl106_3 ),
    inference(unit_resulting_resolution,[],[f3679,f2895])).

fof(f2895,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2654])).

fof(f3705,plain,
    ( ~ spl106_6
    | ~ spl106_7 ),
    inference(avatar_split_clause,[],[f2892,f3696,f3692])).

fof(f2892,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f2653])).

fof(f2653,plain,
    ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | ~ v2_tops_1(sK1,sK0) )
    & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
      | v2_tops_1(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2650,f2652,f2651])).

fof(f2651,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | v2_tops_1(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
            | ~ v2_tops_1(X1,sK0) )
          & ( r1_tarski(X1,k2_tops_1(sK0,X1))
            | v2_tops_1(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2652,plain,
    ( ? [X1] :
        ( ( ~ r1_tarski(X1,k2_tops_1(sK0,X1))
          | ~ v2_tops_1(X1,sK0) )
        & ( r1_tarski(X1,k2_tops_1(sK0,X1))
          | v2_tops_1(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | ~ v2_tops_1(sK1,sK0) )
      & ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
        | v2_tops_1(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2650,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f2649])).

fof(f2649,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_tarski(X1,k2_tops_1(X0,X1))
            | ~ v2_tops_1(X1,X0) )
          & ( r1_tarski(X1,k2_tops_1(X0,X1))
            | v2_tops_1(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2176])).

fof(f2176,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> r1_tarski(X1,k2_tops_1(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2170])).

fof(f2170,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f2169])).

fof(f2169,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f3699,plain,
    ( spl106_6
    | spl106_7 ),
    inference(avatar_split_clause,[],[f2891,f3696,f3692])).

fof(f2891,plain,
    ( r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f2653])).

fof(f3680,plain,(
    spl106_3 ),
    inference(avatar_split_clause,[],[f2890,f3677])).

fof(f2890,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2653])).

fof(f3670,plain,(
    spl106_1 ),
    inference(avatar_split_clause,[],[f2889,f3667])).

fof(f2889,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2653])).
%------------------------------------------------------------------------------
