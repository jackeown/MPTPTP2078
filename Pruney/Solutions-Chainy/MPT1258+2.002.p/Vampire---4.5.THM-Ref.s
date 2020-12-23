%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 167 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :    8
%              Number of atoms          :  269 ( 427 expanded)
%              Number of equality atoms :   60 (  95 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3229,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f57,f61,f65,f69,f82,f112,f163,f207,f255,f276,f839,f2525,f2690,f3228])).

fof(f3228,plain,
    ( spl2_1
    | ~ spl2_36
    | ~ spl2_422
    | ~ spl2_449 ),
    inference(avatar_contradiction_clause,[],[f3227])).

fof(f3227,plain,
    ( $false
    | spl2_1
    | ~ spl2_36
    | ~ spl2_422
    | ~ spl2_449 ),
    inference(subsumption_resolution,[],[f3226,f38])).

fof(f38,plain,
    ( k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_1
  <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f3226,plain,
    ( k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_36
    | ~ spl2_422
    | ~ spl2_449 ),
    inference(forward_demodulation,[],[f3225,f254])).

fof(f254,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_36 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl2_36
  <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).

fof(f3225,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_422
    | ~ spl2_449 ),
    inference(forward_demodulation,[],[f3137,f2524])).

fof(f2524,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_422 ),
    inference(avatar_component_clause,[],[f2522])).

fof(f2522,plain,
    ( spl2_422
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_422])])).

fof(f3137,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))))
    | ~ spl2_449 ),
    inference(resolution,[],[f2685,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f2685,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_449 ),
    inference(avatar_component_clause,[],[f2684])).

fof(f2684,plain,
    ( spl2_449
  <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_449])])).

fof(f2690,plain,
    ( ~ spl2_2
    | spl2_449 ),
    inference(avatar_contradiction_clause,[],[f2689])).

fof(f2689,plain,
    ( $false
    | ~ spl2_2
    | spl2_449 ),
    inference(subsumption_resolution,[],[f2688,f43])).

fof(f43,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f2688,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_449 ),
    inference(resolution,[],[f2686,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f2686,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_449 ),
    inference(avatar_component_clause,[],[f2684])).

fof(f2525,plain,
    ( spl2_422
    | ~ spl2_39
    | ~ spl2_135 ),
    inference(avatar_split_clause,[],[f2520,f836,f273,f2522])).

fof(f273,plain,
    ( spl2_39
  <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f836,plain,
    ( spl2_135
  <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).

fof(f2520,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_39
    | ~ spl2_135 ),
    inference(forward_demodulation,[],[f275,f838])).

fof(f838,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_135 ),
    inference(avatar_component_clause,[],[f836])).

fof(f275,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_39 ),
    inference(avatar_component_clause,[],[f273])).

fof(f839,plain,
    ( spl2_135
    | ~ spl2_2
    | ~ spl2_21
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f834,f205,f160,f41,f836])).

fof(f160,plain,
    ( spl2_21
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f205,plain,
    ( spl2_27
  <=> ! [X0] :
        ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f834,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_21
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f797,f162])).

fof(f162,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f160])).

fof(f797,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_27 ),
    inference(resolution,[],[f206,f43])).

fof(f206,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f205])).

fof(f276,plain,
    ( spl2_39
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f261,f109,f80,f273])).

fof(f80,plain,
    ( spl2_8
  <=> ! [X0] :
        ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f109,plain,
    ( spl2_13
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f261,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)))
    | ~ spl2_8
    | ~ spl2_13 ),
    inference(resolution,[],[f81,f111])).

fof(f111,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f109])).

fof(f81,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f255,plain,
    ( spl2_36
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f232,f59,f41,f252])).

fof(f59,plain,
    ( spl2_5
  <=> ! [X1] :
        ( k1_tops_1(sK0,X1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f232,plain,
    ( k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(resolution,[],[f60,f43])).

fof(f60,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1))) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f207,plain,
    ( spl2_27
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f198,f55,f205])).

fof(f55,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f198,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_4 ),
    inference(resolution,[],[f56,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f56,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f55])).

fof(f163,plain,
    ( spl2_21
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f145,f63,f41,f160])).

fof(f63,plain,
    ( spl2_6
  <=> ! [X2] :
        ( k2_tops_1(sK0,X2) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f145,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(resolution,[],[f64,f43])).

fof(f64,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X2) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X2)) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f112,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f99,f67,f41,f109])).

fof(f67,plain,
    ( spl2_7
  <=> ! [X3] :
        ( m1_subset_1(k2_tops_1(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f99,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(resolution,[],[f68,f43])).

fof(f68,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k2_tops_1(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f82,plain,
    ( spl2_8
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f74,f41,f80])).

fof(f74,plain,
    ( ! [X0] :
        ( k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_2 ),
    inference(resolution,[],[f43,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(f69,plain,
    ( spl2_7
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f53,f46,f67])).

fof(f46,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f53,plain,
    ( ! [X3] :
        ( m1_subset_1(k2_tops_1(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_3 ),
    inference(resolution,[],[f48,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f48,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f65,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f52,f46,f63])).

fof(f52,plain,
    ( ! [X2] :
        ( k2_tops_1(sK0,X2) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_3 ),
    inference(resolution,[],[f48,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f61,plain,
    ( spl2_5
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f51,f46,f59])).

fof(f51,plain,
    ( ! [X1] :
        ( k1_tops_1(sK0,X1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_3 ),
    inference(resolution,[],[f48,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f57,plain,
    ( spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f50,f46,f55])).

fof(f50,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl2_3 ),
    inference(resolution,[],[f48,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

% (8864)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
fof(f49,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k1_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( k1_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k2_tops_1(sK0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( k1_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k2_tops_1(sK0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f44,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f25,f41])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f39,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f26,f36])).

fof(f26,plain,(
    k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (8871)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.45  % (8863)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.45  % (8871)Refutation not found, incomplete strategy% (8871)------------------------------
% 0.21/0.45  % (8871)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (8871)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (8871)Memory used [KB]: 10618
% 0.21/0.45  % (8871)Time elapsed: 0.030 s
% 0.21/0.45  % (8871)------------------------------
% 0.21/0.45  % (8871)------------------------------
% 0.21/0.46  % (8855)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (8858)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.49  % (8860)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.50  % (8870)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (8848)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (8853)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (8854)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (8850)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (8852)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (8856)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.50  % (8851)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (8851)Refutation not found, incomplete strategy% (8851)------------------------------
% 0.21/0.50  % (8851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8851)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (8851)Memory used [KB]: 10490
% 0.21/0.50  % (8851)Time elapsed: 0.093 s
% 0.21/0.50  % (8851)------------------------------
% 0.21/0.50  % (8851)------------------------------
% 0.21/0.51  % (8858)Refutation not found, incomplete strategy% (8858)------------------------------
% 0.21/0.51  % (8858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8858)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8858)Memory used [KB]: 10618
% 0.21/0.51  % (8858)Time elapsed: 0.077 s
% 0.21/0.51  % (8858)------------------------------
% 0.21/0.51  % (8858)------------------------------
% 0.21/0.51  % (8859)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.51  % (8855)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (8861)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (8866)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (8862)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f3229,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f39,f44,f49,f57,f61,f65,f69,f82,f112,f163,f207,f255,f276,f839,f2525,f2690,f3228])).
% 0.21/0.51  fof(f3228,plain,(
% 0.21/0.51    spl2_1 | ~spl2_36 | ~spl2_422 | ~spl2_449),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f3227])).
% 0.21/0.51  fof(f3227,plain,(
% 0.21/0.51    $false | (spl2_1 | ~spl2_36 | ~spl2_422 | ~spl2_449)),
% 0.21/0.51    inference(subsumption_resolution,[],[f3226,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    spl2_1 <=> k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f3226,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) | (~spl2_36 | ~spl2_422 | ~spl2_449)),
% 0.21/0.51    inference(forward_demodulation,[],[f3225,f254])).
% 0.21/0.51  fof(f254,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_36),
% 0.21/0.51    inference(avatar_component_clause,[],[f252])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    spl2_36 <=> k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_36])])).
% 0.21/0.51  fof(f3225,plain,(
% 0.21/0.51    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_422 | ~spl2_449)),
% 0.21/0.51    inference(forward_demodulation,[],[f3137,f2524])).
% 0.21/0.51  fof(f2524,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) | ~spl2_422),
% 0.21/0.51    inference(avatar_component_clause,[],[f2522])).
% 0.21/0.51  fof(f2522,plain,(
% 0.21/0.51    spl2_422 <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_422])])).
% 0.21/0.51  fof(f3137,plain,(
% 0.21/0.51    k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)))) | ~spl2_449),
% 0.21/0.51    inference(resolution,[],[f2685,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.51  fof(f2685,plain,(
% 0.21/0.51    m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_449),
% 0.21/0.51    inference(avatar_component_clause,[],[f2684])).
% 0.21/0.51  fof(f2684,plain,(
% 0.21/0.51    spl2_449 <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_449])])).
% 0.21/0.51  fof(f2690,plain,(
% 0.21/0.51    ~spl2_2 | spl2_449),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f2689])).
% 0.21/0.51  fof(f2689,plain,(
% 0.21/0.51    $false | (~spl2_2 | spl2_449)),
% 0.21/0.51    inference(subsumption_resolution,[],[f2688,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f2688,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_449),
% 0.21/0.51    inference(resolution,[],[f2686,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 0.21/0.51  fof(f2686,plain,(
% 0.21/0.51    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_449),
% 0.21/0.51    inference(avatar_component_clause,[],[f2684])).
% 0.21/0.51  fof(f2525,plain,(
% 0.21/0.51    spl2_422 | ~spl2_39 | ~spl2_135),
% 0.21/0.51    inference(avatar_split_clause,[],[f2520,f836,f273,f2522])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    spl2_39 <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).
% 0.21/0.51  fof(f836,plain,(
% 0.21/0.51    spl2_135 <=> k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_135])])).
% 0.21/0.51  fof(f2520,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) | (~spl2_39 | ~spl2_135)),
% 0.21/0.51    inference(forward_demodulation,[],[f275,f838])).
% 0.21/0.51  fof(f838,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | ~spl2_135),
% 0.21/0.51    inference(avatar_component_clause,[],[f836])).
% 0.21/0.51  fof(f275,plain,(
% 0.21/0.51    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) | ~spl2_39),
% 0.21/0.51    inference(avatar_component_clause,[],[f273])).
% 0.21/0.51  fof(f839,plain,(
% 0.21/0.51    spl2_135 | ~spl2_2 | ~spl2_21 | ~spl2_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f834,f205,f160,f41,f836])).
% 0.21/0.51  fof(f160,plain,(
% 0.21/0.51    spl2_21 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    spl2_27 <=> ! [X0] : (k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.21/0.51  fof(f834,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) | (~spl2_2 | ~spl2_21 | ~spl2_27)),
% 0.21/0.51    inference(forward_demodulation,[],[f797,f162])).
% 0.21/0.51  fof(f162,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~spl2_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f160])).
% 0.21/0.51  fof(f797,plain,(
% 0.21/0.51    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_27)),
% 0.21/0.51    inference(resolution,[],[f206,f43])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl2_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f205])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    spl2_39 | ~spl2_8 | ~spl2_13),
% 0.21/0.51    inference(avatar_split_clause,[],[f261,f109,f80,f273])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl2_8 <=> ! [X0] : (k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.51  fof(f109,plain,(
% 0.21/0.51    spl2_13 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))) | (~spl2_8 | ~spl2_13)),
% 0.21/0.51    inference(resolution,[],[f81,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f109])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0)) ) | ~spl2_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f80])).
% 0.21/0.51  fof(f255,plain,(
% 0.21/0.51    spl2_36 | ~spl2_2 | ~spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f232,f59,f41,f252])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl2_5 <=> ! [X1] : (k1_tops_1(sK0,X1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f232,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | (~spl2_2 | ~spl2_5)),
% 0.21/0.51    inference(resolution,[],[f60,f43])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)))) ) | ~spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f207,plain,(
% 0.21/0.51    spl2_27 | ~spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f198,f55,f205])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl2_4 <=> ! [X0] : (k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f198,plain,(
% 0.21/0.51    ( ! [X0] : (k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),X0),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_4),
% 0.21/0.51    inference(resolution,[],[f56,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0))) ) | ~spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f55])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl2_21 | ~spl2_2 | ~spl2_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f145,f63,f41,f160])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    spl2_6 <=> ! [X2] : (k2_tops_1(sK0,X2) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_6)),
% 0.21/0.51    inference(resolution,[],[f64,f43])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k2_tops_1(sK0,X2) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X2))) ) | ~spl2_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f63])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl2_13 | ~spl2_2 | ~spl2_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f99,f67,f41,f109])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    spl2_7 <=> ! [X3] : (m1_subset_1(k2_tops_1(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl2_2 | ~spl2_7)),
% 0.21/0.51    inference(resolution,[],[f68,f43])).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k2_tops_1(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f67])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    spl2_8 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f74,f41,f80])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0] : (k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,X0)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_2),
% 0.21/0.51    inference(resolution,[],[f43,f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl2_7 | ~spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f53,f46,f67])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    spl2_3 <=> l1_pre_topc(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X3] : (m1_subset_1(k2_tops_1(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_3),
% 0.21/0.51    inference(resolution,[],[f48,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    l1_pre_topc(sK0) | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f46])).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    spl2_6 | ~spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f52,f46,f63])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ( ! [X2] : (k2_tops_1(sK0,X2) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_3),
% 0.21/0.51    inference(resolution,[],[f48,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    spl2_5 | ~spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f46,f59])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ( ! [X1] : (k1_tops_1(sK0,X1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_3),
% 0.21/0.51    inference(resolution,[],[f48,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    spl2_4 | ~spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f50,f46,f55])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0] : (k2_pre_topc(sK0,X0) = k4_subset_1(u1_struct_0(sK0),X0,k2_tops_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl2_3),
% 0.21/0.51    inference(resolution,[],[f48,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 0.21/0.51  % (8864)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    spl2_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f24,f46])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    (k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f22,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k1_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (k1_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ? [X1] : (k1_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),X1,k2_tops_1(sK0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (k1_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.51    inference(negated_conjecture,[],[f9])).
% 0.21/0.51  fof(f9,conjecture,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f25,f41])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ~spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f36])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    k1_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),sK1,k2_tops_1(sK0,sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (8855)------------------------------
% 0.21/0.51  % (8855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8855)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (8855)Memory used [KB]: 8315
% 0.21/0.51  % (8855)Time elapsed: 0.092 s
% 0.21/0.51  % (8855)------------------------------
% 0.21/0.51  % (8855)------------------------------
% 0.21/0.52  % (8847)Success in time 0.16 s
%------------------------------------------------------------------------------
