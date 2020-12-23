%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1295+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:16 EST 2020

% Result     : Theorem 6.50s
% Output     : Refutation 6.50s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 196 expanded)
%              Number of leaves         :   23 (  68 expanded)
%              Depth                    :   10
%              Number of atoms          :  209 ( 395 expanded)
%              Number of equality atoms :   87 ( 170 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10534,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4392,f4402,f4417,f4510,f4618,f4698,f5013,f6087,f10526])).

fof(f10526,plain,
    ( spl182_22
    | ~ spl182_29
    | ~ spl182_47 ),
    inference(avatar_contradiction_clause,[],[f10525])).

fof(f10525,plain,
    ( $false
    | spl182_22
    | ~ spl182_29
    | ~ spl182_47 ),
    inference(subsumption_resolution,[],[f10524,f5336])).

fof(f5336,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f4213,f5335])).

fof(f5335,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f5284,f4485])).

fof(f4485,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f4472,f4484])).

fof(f4484,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f4476,f3540])).

fof(f3540,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f4476,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f3350,f3278])).

fof(f3278,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2282])).

fof(f2282,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3350,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f4472,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f3350,f3277])).

fof(f3277,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2281])).

fof(f2281,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f5284,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f4359,f3278])).

fof(f4359,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f3715,f3716])).

fof(f3716,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f460])).

fof(f460,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f3715,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f465])).

fof(f465,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f4213,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f3499])).

fof(f3499,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f2950])).

fof(f2950,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f377])).

fof(f377,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f10524,plain,
    ( k1_xboole_0 = k1_tarski(k4_xboole_0(sK0,k3_tarski(sK1)))
    | spl182_22
    | ~ spl182_29
    | ~ spl182_47 ),
    inference(forward_demodulation,[],[f10493,f5335])).

fof(f10493,plain,
    ( k1_tarski(k4_xboole_0(sK0,k3_tarski(sK1))) = k4_xboole_0(k1_tarski(k4_xboole_0(sK0,k3_tarski(sK1))),k1_tarski(k4_xboole_0(sK0,k3_tarski(sK1))))
    | spl182_22
    | ~ spl182_29
    | ~ spl182_47 ),
    inference(backward_demodulation,[],[f9512,f10459])).

fof(f10459,plain,
    ( k4_xboole_0(sK0,k3_tarski(sK1)) = k1_setfam_1(k7_setfam_1(sK0,sK1))
    | ~ spl182_47 ),
    inference(backward_demodulation,[],[f6086,f10286])).

fof(f10286,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f4359,f3651])).

fof(f3651,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2459])).

fof(f2459,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f494])).

fof(f494,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f6086,plain,
    ( k7_subset_1(sK0,sK0,k3_tarski(sK1)) = k1_setfam_1(k7_setfam_1(sK0,sK1))
    | ~ spl182_47 ),
    inference(avatar_component_clause,[],[f6084])).

fof(f6084,plain,
    ( spl182_47
  <=> k7_subset_1(sK0,sK0,k3_tarski(sK1)) = k1_setfam_1(k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_47])])).

fof(f9512,plain,
    ( k1_tarski(k1_setfam_1(k7_setfam_1(sK0,sK1))) = k4_xboole_0(k1_tarski(k1_setfam_1(k7_setfam_1(sK0,sK1))),k1_tarski(k4_xboole_0(sK0,k3_tarski(sK1))))
    | spl182_22
    | ~ spl182_29 ),
    inference(forward_demodulation,[],[f9456,f5032])).

fof(f5032,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k1_setfam_1(k7_setfam_1(sK0,sK1))
    | ~ spl182_29 ),
    inference(unit_resulting_resolution,[],[f5012,f3305])).

fof(f3305,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f2296])).

fof(f2296,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f582])).

fof(f582,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f5012,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl182_29 ),
    inference(avatar_component_clause,[],[f5010])).

fof(f5010,plain,
    ( spl182_29
  <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_29])])).

fof(f9456,plain,
    ( k1_tarski(k6_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k4_xboole_0(k1_tarski(k6_setfam_1(sK0,k7_setfam_1(sK0,sK1))),k1_tarski(k4_xboole_0(sK0,k3_tarski(sK1))))
    | spl182_22 ),
    inference(unit_resulting_resolution,[],[f4697,f3500])).

fof(f3500,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2950])).

fof(f4697,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k4_xboole_0(sK0,k3_tarski(sK1))
    | spl182_22 ),
    inference(avatar_component_clause,[],[f4695])).

fof(f4695,plain,
    ( spl182_22
  <=> k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k4_xboole_0(sK0,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_22])])).

fof(f6087,plain,
    ( spl182_47
    | spl182_1
    | ~ spl182_3
    | ~ spl182_29 ),
    inference(avatar_split_clause,[],[f5116,f5010,f4399,f4389,f6084])).

fof(f4389,plain,
    ( spl182_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_1])])).

fof(f4399,plain,
    ( spl182_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_3])])).

fof(f5116,plain,
    ( k7_subset_1(sK0,sK0,k3_tarski(sK1)) = k1_setfam_1(k7_setfam_1(sK0,sK1))
    | spl182_1
    | ~ spl182_3
    | ~ spl182_29 ),
    inference(backward_demodulation,[],[f4700,f5032])).

fof(f4700,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k7_subset_1(sK0,sK0,k3_tarski(sK1))
    | spl182_1
    | ~ spl182_3 ),
    inference(forward_demodulation,[],[f4699,f4498])).

fof(f4498,plain,
    ( k5_setfam_1(sK0,sK1) = k3_tarski(sK1)
    | ~ spl182_3 ),
    inference(unit_resulting_resolution,[],[f4401,f3282])).

fof(f3282,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2287])).

fof(f2287,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f581])).

fof(f581,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f4401,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl182_3 ),
    inference(avatar_component_clause,[],[f4399])).

fof(f4699,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k7_subset_1(sK0,sK0,k5_setfam_1(sK0,sK1))
    | spl182_1
    | ~ spl182_3 ),
    inference(unit_resulting_resolution,[],[f4391,f4401,f4354])).

fof(f4354,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k5_setfam_1(X0,X1)) ) ),
    inference(backward_demodulation,[],[f3302,f3716])).

fof(f3302,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2292])).

fof(f2292,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f2291])).

fof(f2291,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f614])).

fof(f614,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_setfam_1)).

fof(f4391,plain,
    ( k1_xboole_0 != sK1
    | spl182_1 ),
    inference(avatar_component_clause,[],[f4389])).

fof(f5013,plain,
    ( spl182_29
    | ~ spl182_3 ),
    inference(avatar_split_clause,[],[f4531,f4399,f5010])).

fof(f4531,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl182_3 ),
    inference(unit_resulting_resolution,[],[f4401,f3330])).

fof(f3330,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2314])).

fof(f2314,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f565])).

fof(f565,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f4698,plain,
    ( ~ spl182_22
    | spl182_15
    | ~ spl182_18 ),
    inference(avatar_split_clause,[],[f4689,f4615,f4507,f4695])).

fof(f4507,plain,
    ( spl182_15
  <=> k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_15])])).

fof(f4615,plain,
    ( spl182_18
  <=> m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_18])])).

fof(f4689,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k4_xboole_0(sK0,k3_tarski(sK1))
    | spl182_15
    | ~ spl182_18 ),
    inference(backward_demodulation,[],[f4509,f4686])).

fof(f4686,plain,
    ( k3_subset_1(sK0,k3_tarski(sK1)) = k4_xboole_0(sK0,k3_tarski(sK1))
    | ~ spl182_18 ),
    inference(unit_resulting_resolution,[],[f4617,f3278])).

fof(f4617,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl182_18 ),
    inference(avatar_component_clause,[],[f4615])).

fof(f4509,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k3_tarski(sK1))
    | spl182_15 ),
    inference(avatar_component_clause,[],[f4507])).

fof(f4618,plain,
    ( spl182_18
    | ~ spl182_3 ),
    inference(avatar_split_clause,[],[f4504,f4399,f4615])).

fof(f4504,plain,
    ( m1_subset_1(k3_tarski(sK1),k1_zfmisc_1(sK0))
    | ~ spl182_3 ),
    inference(backward_demodulation,[],[f4490,f4498])).

fof(f4490,plain,
    ( m1_subset_1(k5_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl182_3 ),
    inference(unit_resulting_resolution,[],[f4401,f3281])).

fof(f3281,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2286])).

% (14159)Time limit reached!
% (14159)------------------------------
% (14159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f2286,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f563])).

fof(f563,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f4510,plain,
    ( ~ spl182_15
    | ~ spl182_3
    | spl182_6 ),
    inference(avatar_split_clause,[],[f4505,f4414,f4399,f4507])).

fof(f4414,plain,
    ( spl182_6
  <=> k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k5_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_6])])).

fof(f4505,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k3_tarski(sK1))
    | ~ spl182_3
    | spl182_6 ),
    inference(backward_demodulation,[],[f4416,f4498])).

fof(f4416,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k5_setfam_1(sK0,sK1))
    | spl182_6 ),
    inference(avatar_component_clause,[],[f4414])).

fof(f4417,plain,(
    ~ spl182_6 ),
    inference(avatar_split_clause,[],[f3255,f4414])).

fof(f3255,plain,(
    k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k5_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f2847])).

fof(f2847,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k5_setfam_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2259,f2846])).

fof(f2846,plain,
    ( ? [X0,X1] :
        ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k5_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k6_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k5_setfam_1(sK0,sK1))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2259,plain,(
    ? [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k5_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f2258])).

fof(f2258,plain,(
    ? [X0,X1] :
      ( k6_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k5_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2245])).

fof(f2245,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f2244])).

fof(f2244,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k5_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tops_2)).

fof(f4402,plain,(
    spl182_3 ),
    inference(avatar_split_clause,[],[f3253,f4399])).

fof(f3253,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f2847])).

fof(f4392,plain,(
    ~ spl182_1 ),
    inference(avatar_split_clause,[],[f3254,f4389])).

fof(f3254,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f2847])).
%------------------------------------------------------------------------------
