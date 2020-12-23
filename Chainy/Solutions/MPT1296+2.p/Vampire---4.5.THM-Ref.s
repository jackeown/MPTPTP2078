%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1296+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:16 EST 2020

% Result     : Theorem 6.37s
% Output     : Refutation 6.37s
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
fof(f10560,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4396,f4406,f4421,f4514,f4622,f4698,f5027,f6118,f10559])).

fof(f10559,plain,
    ( spl182_22
    | ~ spl182_30
    | ~ spl182_50 ),
    inference(avatar_contradiction_clause,[],[f10558])).

fof(f10558,plain,
    ( $false
    | spl182_22
    | ~ spl182_30
    | ~ spl182_50 ),
    inference(subsumption_resolution,[],[f10557,f5353])).

fof(f5353,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f4217,f5352])).

fof(f5352,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f5301,f4489])).

fof(f4489,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(backward_demodulation,[],[f4476,f4488])).

fof(f4488,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f4480,f3544])).

fof(f3544,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f100])).

fof(f100,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f4480,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f3354,f3281])).

fof(f3281,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2283])).

fof(f2283,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f3354,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f522])).

fof(f522,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f4476,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f3354,f3280])).

fof(f3280,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f2282])).

fof(f2282,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f487])).

fof(f487,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f5301,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f4363,f3281])).

fof(f4363,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f3578,f3579])).

fof(f3579,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f460])).

fof(f460,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f3578,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f465])).

fof(f465,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f4217,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f3503])).

fof(f3503,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f2953])).

fof(f2953,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f10557,plain,
    ( k1_xboole_0 = k1_tarski(k4_xboole_0(sK0,k1_setfam_1(sK1)))
    | spl182_22
    | ~ spl182_30
    | ~ spl182_50 ),
    inference(forward_demodulation,[],[f10523,f5352])).

fof(f10523,plain,
    ( k1_tarski(k4_xboole_0(sK0,k1_setfam_1(sK1))) = k4_xboole_0(k1_tarski(k4_xboole_0(sK0,k1_setfam_1(sK1))),k1_tarski(k4_xboole_0(sK0,k1_setfam_1(sK1))))
    | spl182_22
    | ~ spl182_30
    | ~ spl182_50 ),
    inference(backward_demodulation,[],[f9552,f10489])).

fof(f10489,plain,
    ( k4_xboole_0(sK0,k1_setfam_1(sK1)) = k3_tarski(k7_setfam_1(sK0,sK1))
    | ~ spl182_50 ),
    inference(backward_demodulation,[],[f6117,f10316])).

fof(f10316,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) ),
    inference(unit_resulting_resolution,[],[f4363,f3546])).

fof(f3546,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2445])).

fof(f2445,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f494])).

fof(f494,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f6117,plain,
    ( k7_subset_1(sK0,sK0,k1_setfam_1(sK1)) = k3_tarski(k7_setfam_1(sK0,sK1))
    | ~ spl182_50 ),
    inference(avatar_component_clause,[],[f6115])).

fof(f6115,plain,
    ( spl182_50
  <=> k7_subset_1(sK0,sK0,k1_setfam_1(sK1)) = k3_tarski(k7_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_50])])).

fof(f9552,plain,
    ( k1_tarski(k3_tarski(k7_setfam_1(sK0,sK1))) = k4_xboole_0(k1_tarski(k3_tarski(k7_setfam_1(sK0,sK1))),k1_tarski(k4_xboole_0(sK0,k1_setfam_1(sK1))))
    | spl182_22
    | ~ spl182_30 ),
    inference(forward_demodulation,[],[f9495,f5042])).

fof(f5042,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_tarski(k7_setfam_1(sK0,sK1))
    | ~ spl182_30 ),
    inference(unit_resulting_resolution,[],[f5026,f3298])).

fof(f3298,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2300])).

fof(f2300,plain,(
    ! [X0,X1] :
      ( k3_tarski(X1) = k5_setfam_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f581])).

fof(f581,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k3_tarski(X1) = k5_setfam_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_setfam_1)).

fof(f5026,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl182_30 ),
    inference(avatar_component_clause,[],[f5024])).

fof(f5024,plain,
    ( spl182_30
  <=> m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_30])])).

fof(f9495,plain,
    ( k1_tarski(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k4_xboole_0(k1_tarski(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))),k1_tarski(k4_xboole_0(sK0,k1_setfam_1(sK1))))
    | spl182_22 ),
    inference(unit_resulting_resolution,[],[f4697,f3504])).

fof(f3504,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2953])).

fof(f4697,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k4_xboole_0(sK0,k1_setfam_1(sK1))
    | spl182_22 ),
    inference(avatar_component_clause,[],[f4695])).

fof(f4695,plain,
    ( spl182_22
  <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k4_xboole_0(sK0,k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_22])])).

fof(f6118,plain,
    ( spl182_50
    | spl182_1
    | ~ spl182_3
    | ~ spl182_30 ),
    inference(avatar_split_clause,[],[f5126,f5024,f4403,f4393,f6115])).

fof(f4393,plain,
    ( spl182_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_1])])).

fof(f4403,plain,
    ( spl182_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_3])])).

fof(f5126,plain,
    ( k7_subset_1(sK0,sK0,k1_setfam_1(sK1)) = k3_tarski(k7_setfam_1(sK0,sK1))
    | spl182_1
    | ~ spl182_3
    | ~ spl182_30 ),
    inference(backward_demodulation,[],[f4714,f5042])).

fof(f4714,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k7_subset_1(sK0,sK0,k1_setfam_1(sK1))
    | spl182_1
    | ~ spl182_3 ),
    inference(forward_demodulation,[],[f4713,f4502])).

fof(f4502,plain,
    ( k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl182_3 ),
    inference(unit_resulting_resolution,[],[f4405,f3288])).

fof(f3288,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f2294])).

fof(f2294,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f582])).

fof(f582,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f4405,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl182_3 ),
    inference(avatar_component_clause,[],[f4403])).

fof(f4713,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k7_subset_1(sK0,sK0,k6_setfam_1(sK0,sK1))
    | spl182_1
    | ~ spl182_3 ),
    inference(unit_resulting_resolution,[],[f4395,f4405,f4359])).

fof(f4359,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k6_setfam_1(X0,X1)) ) ),
    inference(backward_demodulation,[],[f3285,f3579])).

fof(f3285,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2290])).

fof(f2290,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f2289])).

fof(f2289,plain,(
    ! [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f615])).

fof(f615,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_setfam_1)).

fof(f4395,plain,
    ( k1_xboole_0 != sK1
    | spl182_1 ),
    inference(avatar_component_clause,[],[f4393])).

fof(f5027,plain,
    ( spl182_30
    | ~ spl182_3 ),
    inference(avatar_split_clause,[],[f4535,f4403,f5024])).

fof(f4535,plain,
    ( m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl182_3 ),
    inference(unit_resulting_resolution,[],[f4405,f3334])).

fof(f3334,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2317])).

fof(f2317,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f565])).

fof(f565,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f4698,plain,
    ( ~ spl182_22
    | spl182_15
    | ~ spl182_18 ),
    inference(avatar_split_clause,[],[f4689,f4619,f4511,f4695])).

fof(f4511,plain,
    ( spl182_15
  <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k1_setfam_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_15])])).

fof(f4619,plain,
    ( spl182_18
  <=> m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_18])])).

fof(f4689,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k4_xboole_0(sK0,k1_setfam_1(sK1))
    | spl182_15
    | ~ spl182_18 ),
    inference(backward_demodulation,[],[f4513,f4686])).

fof(f4686,plain,
    ( k3_subset_1(sK0,k1_setfam_1(sK1)) = k4_xboole_0(sK0,k1_setfam_1(sK1))
    | ~ spl182_18 ),
    inference(unit_resulting_resolution,[],[f4621,f3281])).

fof(f4621,plain,
    ( m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl182_18 ),
    inference(avatar_component_clause,[],[f4619])).

fof(f4513,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k1_setfam_1(sK1))
    | spl182_15 ),
    inference(avatar_component_clause,[],[f4511])).

fof(f4622,plain,
    ( spl182_18
    | ~ spl182_3 ),
    inference(avatar_split_clause,[],[f4508,f4403,f4619])).

fof(f4508,plain,
    ( m1_subset_1(k1_setfam_1(sK1),k1_zfmisc_1(sK0))
    | ~ spl182_3 ),
    inference(backward_demodulation,[],[f4494,f4502])).

fof(f4494,plain,
    ( m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl182_3 ),
    inference(unit_resulting_resolution,[],[f4405,f3287])).

fof(f3287,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f2293])).

fof(f2293,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f564])).

fof(f564,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k6_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_setfam_1)).

fof(f4514,plain,
    ( ~ spl182_15
    | ~ spl182_3
    | spl182_6 ),
    inference(avatar_split_clause,[],[f4509,f4418,f4403,f4511])).

fof(f4418,plain,
    ( spl182_6
  <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl182_6])])).

fof(f4509,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k1_setfam_1(sK1))
    | ~ spl182_3
    | spl182_6 ),
    inference(backward_demodulation,[],[f4420,f4502])).

fof(f4420,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | spl182_6 ),
    inference(avatar_component_clause,[],[f4418])).

fof(f4421,plain,(
    ~ spl182_6 ),
    inference(avatar_split_clause,[],[f3258,f4418])).

fof(f3258,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f2850])).

fof(f2850,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f2260,f2849])).

fof(f2849,plain,
    ( ? [X0,X1] :
        ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2260,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f2259])).

fof(f2259,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k3_subset_1(X0,k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2246])).

fof(f2246,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f2245])).

fof(f2245,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k3_subset_1(X0,k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_tops_2)).

fof(f4406,plain,(
    spl182_3 ),
    inference(avatar_split_clause,[],[f3256,f4403])).

fof(f3256,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f2850])).

fof(f4396,plain,(
    ~ spl182_1 ),
    inference(avatar_split_clause,[],[f3257,f4393])).

fof(f3257,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f2850])).
%------------------------------------------------------------------------------
