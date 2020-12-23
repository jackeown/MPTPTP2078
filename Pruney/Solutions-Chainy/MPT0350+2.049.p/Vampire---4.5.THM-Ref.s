%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:57 EST 2020

% Result     : Theorem 4.89s
% Output     : Refutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  175 ( 347 expanded)
%              Number of leaves         :   41 ( 134 expanded)
%              Depth                    :   13
%              Number of atoms          :  394 ( 715 expanded)
%              Number of equality atoms :  100 ( 227 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5172,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f92,f121,f238,f256,f302,f2628,f3405,f3409,f3428,f3470,f3746,f3765,f3778,f3956,f3978,f3988,f4629,f5170])).

fof(f5170,plain,
    ( ~ spl3_61
    | spl3_64
    | ~ spl3_84 ),
    inference(avatar_contradiction_clause,[],[f5169])).

fof(f5169,plain,
    ( $false
    | ~ spl3_61
    | spl3_64
    | ~ spl3_84 ),
    inference(subsumption_resolution,[],[f5168,f3745])).

fof(f3745,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK0)
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f3743])).

fof(f3743,plain,
    ( spl3_61
  <=> r1_tarski(k5_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f5168,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK0)
    | spl3_64
    | ~ spl3_84 ),
    inference(subsumption_resolution,[],[f5151,f3762])).

fof(f3762,plain,
    ( ~ r1_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | spl3_64 ),
    inference(avatar_component_clause,[],[f3761])).

fof(f3761,plain,
    ( spl3_64
  <=> r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f5151,plain,
    ( r1_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ r1_tarski(k5_xboole_0(sK0,sK1),sK0)
    | ~ spl3_84 ),
    inference(superposition,[],[f289,f4628])).

fof(f4628,plain,
    ( sK1 = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0)
    | ~ spl3_84 ),
    inference(avatar_component_clause,[],[f4626])).

fof(f4626,plain,
    ( spl3_84
  <=> sK1 = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f289,plain,(
    ! [X2,X1] :
      ( r1_xboole_0(k5_xboole_0(X1,X2),X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f203,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f203,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f73,f68])).

fof(f68,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f73,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f4629,plain,
    ( spl3_84
    | ~ spl3_69
    | ~ spl3_71 ),
    inference(avatar_split_clause,[],[f4624,f3985,f3975,f4626])).

fof(f3975,plain,
    ( spl3_69
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f3985,plain,
    ( spl3_71
  <=> sK1 = k5_xboole_0(k3_subset_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f4624,plain,
    ( sK1 = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0)
    | ~ spl3_69
    | ~ spl3_71 ),
    inference(forward_demodulation,[],[f3987,f3977])).

fof(f3977,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f3975])).

fof(f3987,plain,
    ( sK1 = k5_xboole_0(k3_subset_1(sK0,sK1),sK0)
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f3985])).

fof(f3988,plain,
    ( spl3_71
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f3965,f2273,f3985])).

fof(f2273,plain,
    ( spl3_38
  <=> sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f3965,plain,
    ( sK1 = k5_xboole_0(k3_subset_1(sK0,sK1),sK0)
    | ~ spl3_38 ),
    inference(superposition,[],[f213,f2274])).

fof(f2274,plain,
    ( sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f2273])).

fof(f213,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f185,f51])).

fof(f51,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f185,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f168,f93])).

fof(f93,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f51,f70])).

fof(f70,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f168,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f49,f71])).

fof(f71,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f3978,plain,
    ( spl3_69
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f3973,f2273,f3975])).

fof(f3973,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f3963,f51])).

fof(f3963,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK1,sK0)
    | ~ spl3_38 ),
    inference(superposition,[],[f185,f2274])).

fof(f3956,plain,
    ( ~ spl3_5
    | spl3_40 ),
    inference(avatar_contradiction_clause,[],[f3955])).

fof(f3955,plain,
    ( $false
    | ~ spl3_5
    | spl3_40 ),
    inference(subsumption_resolution,[],[f3954,f120])).

fof(f120,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl3_5
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f3954,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_40 ),
    inference(subsumption_resolution,[],[f3950,f213])).

fof(f3950,plain,
    ( sK0 != k5_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK0)
    | spl3_40 ),
    inference(superposition,[],[f2284,f342])).

% (22693)Time limit reached!
% (22693)------------------------------
% (22693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (22882)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% (22672)Termination reason: Time limit
% (22672)Termination phase: Saturation

% (22672)Memory used [KB]: 11513
% (22672)Time elapsed: 0.600 s
% (22672)------------------------------
% (22672)------------------------------
fof(f342,plain,(
    ! [X14,X15] :
      ( k5_xboole_0(X14,X15) = k4_xboole_0(X14,X15)
      | ~ r1_tarski(X15,X14) ) ),
    inference(superposition,[],[f69,f129])).

fof(f129,plain,(
    ! [X6,X5] :
      ( k3_xboole_0(X6,X5) = X5
      | ~ r1_tarski(X5,X6) ) ),
    inference(superposition,[],[f67,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

% (22880)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
fof(f2284,plain,
    ( sK0 != k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | spl3_40 ),
    inference(avatar_component_clause,[],[f2282])).

fof(f2282,plain,
    ( spl3_40
  <=> sK0 = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f3778,plain,
    ( ~ spl3_64
    | ~ spl3_5
    | spl3_39 ),
    inference(avatar_split_clause,[],[f3777,f2278,f118,f3761])).

fof(f2278,plain,
    ( spl3_39
  <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f3777,plain,
    ( ~ r1_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ spl3_5
    | spl3_39 ),
    inference(subsumption_resolution,[],[f3772,f120])).

fof(f3772,plain,
    ( ~ r1_xboole_0(sK1,k5_xboole_0(sK0,sK1))
    | ~ r1_tarski(sK1,sK0)
    | spl3_39 ),
    inference(superposition,[],[f2280,f342])).

fof(f2280,plain,
    ( ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f2278])).

fof(f3765,plain,
    ( ~ spl3_39
    | ~ spl3_40
    | spl3_10 ),
    inference(avatar_split_clause,[],[f3462,f245,f2282,f2278])).

fof(f245,plain,
    ( spl3_10
  <=> sK0 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f3462,plain,
    ( sK0 != k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | spl3_10 ),
    inference(superposition,[],[f247,f2236])).

% (22693)Termination reason: Time limit
fof(f2236,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(X3,X4) = k2_xboole_0(X3,X4)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(backward_demodulation,[],[f199,f2159])).

fof(f2159,plain,(
    ! [X7] : k4_xboole_0(X7,k1_xboole_0) = X7 ),
    inference(forward_demodulation,[],[f2131,f70])).

fof(f2131,plain,(
    ! [X7] : k5_xboole_0(X7,k1_xboole_0) = k4_xboole_0(X7,k1_xboole_0) ),
    inference(superposition,[],[f69,f2107])).

fof(f2107,plain,(
    ! [X7] : k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0) ),
    inference(backward_demodulation,[],[f474,f1944])).

fof(f1944,plain,(
    ! [X6] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6) ),
    inference(backward_demodulation,[],[f139,f1925])).

fof(f1925,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f562,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f66,f52])).

fof(f52,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f66,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f562,plain,(
    ! [X6] : r1_xboole_0(k3_xboole_0(k1_xboole_0,X6),k3_xboole_0(k1_xboole_0,X6)) ),
    inference(superposition,[],[f286,f148])).

fof(f148,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f48,f52])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f286,plain,(
    ! [X10] : r1_xboole_0(X10,k3_xboole_0(k1_xboole_0,X10)) ),
    inference(superposition,[],[f203,f93])).

fof(f139,plain,(
    ! [X6] : k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f69,f93])).

fof(f474,plain,(
    ! [X7] : k3_xboole_0(X7,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f137,f93])).

fof(f137,plain,(
    ! [X6,X5] : k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X6,X5)) ),
    inference(superposition,[],[f69,f50])).

fof(f199,plain,(
    ! [X4,X3] :
      ( k5_xboole_0(X3,X4) = k4_xboole_0(k2_xboole_0(X3,X4),k1_xboole_0)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f68,f66])).

fof(f247,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f245])).

fof(f3746,plain,
    ( spl3_61
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f3741,f324,f118,f3743])).

fof(f324,plain,
    ( spl3_14
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f3741,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK0)
    | ~ spl3_5
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f3694,f120])).

fof(f3694,plain,
    ( r1_tarski(k5_xboole_0(sK0,sK1),sK0)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl3_14 ),
    inference(superposition,[],[f326,f342])).

fof(f326,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f324])).

fof(f3470,plain,
    ( ~ spl3_40
    | ~ spl3_2
    | spl3_38 ),
    inference(avatar_split_clause,[],[f3469,f2273,f83,f2282])).

fof(f83,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f3469,plain,
    ( sK0 != k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl3_2
    | spl3_38 ),
    inference(subsumption_resolution,[],[f3468,f85])).

fof(f85,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f3468,plain,
    ( sK0 != k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_38 ),
    inference(superposition,[],[f2275,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f2275,plain,
    ( sK0 != k5_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f2273])).

fof(f3428,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f3427,f299,f83,f324])).

fof(f299,plain,
    ( spl3_13
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f3427,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f3415,f85])).

fof(f3415,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_13 ),
    inference(superposition,[],[f301,f54])).

fof(f301,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f299])).

fof(f3409,plain,
    ( ~ spl3_10
    | ~ spl3_2
    | spl3_8 ),
    inference(avatar_split_clause,[],[f3408,f235,f83,f245])).

fof(f235,plain,
    ( spl3_8
  <=> sK0 = k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f3408,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl3_2
    | spl3_8 ),
    inference(subsumption_resolution,[],[f3406,f85])).

fof(f3406,plain,
    ( sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_8 ),
    inference(superposition,[],[f237,f54])).

fof(f237,plain,
    ( sK0 != k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f235])).

fof(f3405,plain,
    ( spl3_11
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f3404,f231,f263])).

fof(f263,plain,
    ( spl3_11
  <=> r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f231,plain,
    ( spl3_7
  <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f3404,plain,
    ( r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(subsumption_resolution,[],[f3401,f65])).

fof(f65,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f3401,plain,
    ( r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(resolution,[],[f232,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f232,plain,
    ( m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f231])).

fof(f2628,plain,
    ( spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f2627,f83,f109])).

fof(f109,plain,
    ( spl3_4
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f2627,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f2625,f65])).

fof(f2625,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl3_2 ),
    inference(resolution,[],[f85,f57])).

fof(f302,plain,
    ( spl3_13
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f295,f263,f299])).

fof(f295,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK0)
    | ~ spl3_11 ),
    inference(resolution,[],[f265,f76])).

fof(f76,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_zfmisc_1(X0))
      | r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r1_tarski(X3,X0)
      | ~ r2_hidden(X3,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK2(X0,X1),X0)
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( r1_tarski(sK2(X0,X1),X0)
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK2(X0,X1),X0)
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( r1_tarski(sK2(X0,X1),X0)
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f265,plain,
    ( r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f263])).

fof(f256,plain,
    ( ~ spl3_2
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl3_2
    | spl3_7 ),
    inference(subsumption_resolution,[],[f250,f85])).

fof(f250,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_7 ),
    inference(resolution,[],[f233,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f233,plain,
    ( ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f231])).

fof(f238,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | ~ spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f229,f89,f83,f235,f231])).

fof(f89,plain,
    ( spl3_3
  <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f229,plain,
    ( sK0 != k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl3_2
    | spl3_3 ),
    inference(subsumption_resolution,[],[f227,f85])).

fof(f227,plain,
    ( sK0 != k2_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl3_3 ),
    inference(superposition,[],[f91,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f91,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f121,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f115,f109,f118])).

fof(f115,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_4 ),
    inference(resolution,[],[f111,f76])).

fof(f111,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f92,plain,
    ( ~ spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f87,f78,f89])).

fof(f78,plain,
    ( spl3_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f87,plain,
    ( sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl3_1 ),
    inference(backward_demodulation,[],[f80,f56])).

fof(f56,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f80,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f86,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f46,f83])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f39])).

fof(f39,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

fof(f81,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f47,f78])).

fof(f47,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n001.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:18:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (22670)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (22686)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.50  % (22694)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.51  % (22665)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (22669)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (22676)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (22668)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.52  % (22675)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (22691)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (22688)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.52  % (22690)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.52  % (22666)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (22667)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (22687)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (22674)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (22679)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (22678)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (22687)Refutation not found, incomplete strategy% (22687)------------------------------
% 0.20/0.53  % (22687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (22684)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (22671)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (22687)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (22687)Memory used [KB]: 10746
% 0.20/0.53  % (22687)Time elapsed: 0.089 s
% 0.20/0.53  % (22687)------------------------------
% 0.20/0.53  % (22687)------------------------------
% 0.20/0.54  % (22682)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.54  % (22689)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (22693)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (22682)Refutation not found, incomplete strategy% (22682)------------------------------
% 0.20/0.54  % (22682)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (22682)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (22682)Memory used [KB]: 10618
% 0.20/0.54  % (22682)Time elapsed: 0.105 s
% 0.20/0.54  % (22682)------------------------------
% 0.20/0.54  % (22682)------------------------------
% 0.20/0.54  % (22692)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.54  % (22672)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (22681)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (22685)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (22677)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (22683)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (22673)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (22680)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (22680)Refutation not found, incomplete strategy% (22680)------------------------------
% 0.20/0.56  % (22680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (22680)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (22680)Memory used [KB]: 6140
% 0.20/0.56  % (22680)Time elapsed: 0.003 s
% 0.20/0.56  % (22680)------------------------------
% 0.20/0.56  % (22680)------------------------------
% 2.19/0.66  % (22719)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.19/0.68  % (22720)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.19/0.71  % (22733)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.40/0.82  % (22670)Time limit reached!
% 3.40/0.82  % (22670)------------------------------
% 3.40/0.82  % (22670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.40/0.83  % (22670)Termination reason: Time limit
% 3.40/0.83  
% 3.40/0.83  % (22670)Memory used [KB]: 9210
% 3.40/0.83  % (22670)Time elapsed: 0.421 s
% 3.40/0.83  % (22670)------------------------------
% 3.40/0.83  % (22670)------------------------------
% 3.92/0.91  % (22666)Time limit reached!
% 3.92/0.91  % (22666)------------------------------
% 3.92/0.91  % (22666)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.92/0.92  % (22665)Time limit reached!
% 3.92/0.92  % (22665)------------------------------
% 3.92/0.92  % (22665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.92/0.92  % (22675)Time limit reached!
% 3.92/0.92  % (22675)------------------------------
% 3.92/0.92  % (22675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.92/0.93  % (22665)Termination reason: Time limit
% 3.92/0.93  
% 3.92/0.93  % (22665)Memory used [KB]: 3837
% 3.92/0.93  % (22665)Time elapsed: 0.508 s
% 3.92/0.93  % (22665)------------------------------
% 3.92/0.93  % (22665)------------------------------
% 3.92/0.93  % (22666)Termination reason: Time limit
% 3.92/0.93  
% 3.92/0.93  % (22666)Memory used [KB]: 8955
% 3.92/0.93  % (22666)Time elapsed: 0.505 s
% 3.92/0.93  % (22666)------------------------------
% 3.92/0.93  % (22666)------------------------------
% 3.92/0.93  % (22675)Termination reason: Time limit
% 3.92/0.93  
% 3.92/0.93  % (22675)Memory used [KB]: 12920
% 3.92/0.93  % (22675)Time elapsed: 0.530 s
% 3.92/0.93  % (22675)------------------------------
% 3.92/0.93  % (22675)------------------------------
% 3.92/0.93  % (22677)Time limit reached!
% 3.92/0.93  % (22677)------------------------------
% 3.92/0.93  % (22677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.92/0.93  % (22677)Termination reason: Time limit
% 3.92/0.93  
% 3.92/0.93  % (22677)Memory used [KB]: 10490
% 3.92/0.93  % (22677)Time elapsed: 0.530 s
% 3.92/0.93  % (22677)------------------------------
% 3.92/0.93  % (22677)------------------------------
% 4.66/0.97  % (22853)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.89/1.00  % (22681)Time limit reached!
% 4.89/1.00  % (22681)------------------------------
% 4.89/1.00  % (22681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.01  % (22681)Termination reason: Time limit
% 4.89/1.01  % (22681)Termination phase: Saturation
% 4.89/1.01  
% 4.89/1.01  % (22672)Time limit reached!
% 4.89/1.01  % (22672)------------------------------
% 4.89/1.01  % (22672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.01  % (22681)Memory used [KB]: 14583
% 4.89/1.01  % (22681)Time elapsed: 0.600 s
% 4.89/1.01  % (22681)------------------------------
% 4.89/1.01  % (22681)------------------------------
% 4.89/1.02  % (22733)Refutation found. Thanks to Tanya!
% 4.89/1.02  % SZS status Theorem for theBenchmark
% 4.89/1.02  % SZS output start Proof for theBenchmark
% 4.89/1.02  fof(f5172,plain,(
% 4.89/1.02    $false),
% 4.89/1.02    inference(avatar_sat_refutation,[],[f81,f86,f92,f121,f238,f256,f302,f2628,f3405,f3409,f3428,f3470,f3746,f3765,f3778,f3956,f3978,f3988,f4629,f5170])).
% 4.89/1.02  fof(f5170,plain,(
% 4.89/1.02    ~spl3_61 | spl3_64 | ~spl3_84),
% 4.89/1.02    inference(avatar_contradiction_clause,[],[f5169])).
% 4.89/1.02  fof(f5169,plain,(
% 4.89/1.02    $false | (~spl3_61 | spl3_64 | ~spl3_84)),
% 4.89/1.02    inference(subsumption_resolution,[],[f5168,f3745])).
% 4.89/1.02  fof(f3745,plain,(
% 4.89/1.02    r1_tarski(k5_xboole_0(sK0,sK1),sK0) | ~spl3_61),
% 4.89/1.02    inference(avatar_component_clause,[],[f3743])).
% 4.89/1.02  fof(f3743,plain,(
% 4.89/1.02    spl3_61 <=> r1_tarski(k5_xboole_0(sK0,sK1),sK0)),
% 4.89/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 4.89/1.02  fof(f5168,plain,(
% 4.89/1.02    ~r1_tarski(k5_xboole_0(sK0,sK1),sK0) | (spl3_64 | ~spl3_84)),
% 4.89/1.02    inference(subsumption_resolution,[],[f5151,f3762])).
% 4.89/1.02  fof(f3762,plain,(
% 4.89/1.02    ~r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | spl3_64),
% 4.89/1.02    inference(avatar_component_clause,[],[f3761])).
% 4.89/1.02  fof(f3761,plain,(
% 4.89/1.02    spl3_64 <=> r1_xboole_0(sK1,k5_xboole_0(sK0,sK1))),
% 4.89/1.02    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 4.89/1.02  fof(f5151,plain,(
% 4.89/1.02    r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~r1_tarski(k5_xboole_0(sK0,sK1),sK0) | ~spl3_84),
% 4.89/1.02    inference(superposition,[],[f289,f4628])).
% 4.89/1.02  fof(f4628,plain,(
% 4.89/1.02    sK1 = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0) | ~spl3_84),
% 4.89/1.02    inference(avatar_component_clause,[],[f4626])).
% 4.89/1.03  fof(f4626,plain,(
% 4.89/1.03    spl3_84 <=> sK1 = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0)),
% 4.89/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 4.89/1.03  fof(f289,plain,(
% 4.89/1.03    ( ! [X2,X1] : (r1_xboole_0(k5_xboole_0(X1,X2),X1) | ~r1_tarski(X1,X2)) )),
% 4.89/1.03    inference(superposition,[],[f203,f67])).
% 4.89/1.03  fof(f67,plain,(
% 4.89/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.89/1.03    inference(cnf_transformation,[],[f38])).
% 4.89/1.03  fof(f38,plain,(
% 4.89/1.03    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.89/1.03    inference(ennf_transformation,[],[f8])).
% 4.89/1.03  fof(f8,axiom,(
% 4.89/1.03    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 4.89/1.03  fof(f203,plain,(
% 4.89/1.03    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.89/1.03    inference(superposition,[],[f73,f68])).
% 4.89/1.03  fof(f68,plain,(
% 4.89/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.89/1.03    inference(cnf_transformation,[],[f5])).
% 4.89/1.03  fof(f5,axiom,(
% 4.89/1.03    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 4.89/1.03  fof(f73,plain,(
% 4.89/1.03    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 4.89/1.03    inference(cnf_transformation,[],[f10])).
% 4.89/1.03  fof(f10,axiom,(
% 4.89/1.03    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 4.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 4.89/1.03  fof(f4629,plain,(
% 4.89/1.03    spl3_84 | ~spl3_69 | ~spl3_71),
% 4.89/1.03    inference(avatar_split_clause,[],[f4624,f3985,f3975,f4626])).
% 4.89/1.03  fof(f3975,plain,(
% 4.89/1.03    spl3_69 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1)),
% 4.89/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 4.89/1.03  fof(f3985,plain,(
% 4.89/1.03    spl3_71 <=> sK1 = k5_xboole_0(k3_subset_1(sK0,sK1),sK0)),
% 4.89/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 4.89/1.03  fof(f4624,plain,(
% 4.89/1.03    sK1 = k5_xboole_0(k5_xboole_0(sK0,sK1),sK0) | (~spl3_69 | ~spl3_71)),
% 4.89/1.03    inference(forward_demodulation,[],[f3987,f3977])).
% 4.89/1.03  fof(f3977,plain,(
% 4.89/1.03    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl3_69),
% 4.89/1.03    inference(avatar_component_clause,[],[f3975])).
% 4.89/1.03  fof(f3987,plain,(
% 4.89/1.03    sK1 = k5_xboole_0(k3_subset_1(sK0,sK1),sK0) | ~spl3_71),
% 4.89/1.03    inference(avatar_component_clause,[],[f3985])).
% 4.89/1.03  fof(f3988,plain,(
% 4.89/1.03    spl3_71 | ~spl3_38),
% 4.89/1.03    inference(avatar_split_clause,[],[f3965,f2273,f3985])).
% 4.89/1.03  fof(f2273,plain,(
% 4.89/1.03    spl3_38 <=> sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 4.89/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 4.89/1.03  fof(f3965,plain,(
% 4.89/1.03    sK1 = k5_xboole_0(k3_subset_1(sK0,sK1),sK0) | ~spl3_38),
% 4.89/1.03    inference(superposition,[],[f213,f2274])).
% 4.89/1.03  fof(f2274,plain,(
% 4.89/1.03    sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~spl3_38),
% 4.89/1.03    inference(avatar_component_clause,[],[f2273])).
% 4.89/1.03  fof(f213,plain,(
% 4.89/1.03    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 4.89/1.03    inference(superposition,[],[f185,f51])).
% 4.89/1.03  fof(f51,plain,(
% 4.89/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 4.89/1.03    inference(cnf_transformation,[],[f2])).
% 4.89/1.03  fof(f2,axiom,(
% 4.89/1.03    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 4.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 4.89/1.03  fof(f185,plain,(
% 4.89/1.03    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 4.89/1.03    inference(forward_demodulation,[],[f168,f93])).
% 4.89/1.03  fof(f93,plain,(
% 4.89/1.03    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 4.89/1.03    inference(superposition,[],[f51,f70])).
% 4.89/1.03  fof(f70,plain,(
% 4.89/1.03    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.89/1.03    inference(cnf_transformation,[],[f9])).
% 4.89/1.03  fof(f9,axiom,(
% 4.89/1.03    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 4.89/1.03  fof(f168,plain,(
% 4.89/1.03    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 4.89/1.03    inference(superposition,[],[f49,f71])).
% 4.89/1.03  fof(f71,plain,(
% 4.89/1.03    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.89/1.03    inference(cnf_transformation,[],[f12])).
% 4.89/1.03  fof(f12,axiom,(
% 4.89/1.03    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 4.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 4.89/1.03  fof(f49,plain,(
% 4.89/1.03    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.89/1.03    inference(cnf_transformation,[],[f11])).
% 4.89/1.03  fof(f11,axiom,(
% 4.89/1.03    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.89/1.03  fof(f3978,plain,(
% 4.89/1.03    spl3_69 | ~spl3_38),
% 4.89/1.03    inference(avatar_split_clause,[],[f3973,f2273,f3975])).
% 4.89/1.03  fof(f3973,plain,(
% 4.89/1.03    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,sK1) | ~spl3_38),
% 4.89/1.03    inference(forward_demodulation,[],[f3963,f51])).
% 4.89/1.03  fof(f3963,plain,(
% 4.89/1.03    k3_subset_1(sK0,sK1) = k5_xboole_0(sK1,sK0) | ~spl3_38),
% 4.89/1.03    inference(superposition,[],[f185,f2274])).
% 4.89/1.03  fof(f3956,plain,(
% 4.89/1.03    ~spl3_5 | spl3_40),
% 4.89/1.03    inference(avatar_contradiction_clause,[],[f3955])).
% 4.89/1.03  fof(f3955,plain,(
% 4.89/1.03    $false | (~spl3_5 | spl3_40)),
% 4.89/1.03    inference(subsumption_resolution,[],[f3954,f120])).
% 4.89/1.03  fof(f120,plain,(
% 4.89/1.03    r1_tarski(sK1,sK0) | ~spl3_5),
% 4.89/1.03    inference(avatar_component_clause,[],[f118])).
% 4.89/1.03  fof(f118,plain,(
% 4.89/1.03    spl3_5 <=> r1_tarski(sK1,sK0)),
% 4.89/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 4.89/1.03  fof(f3954,plain,(
% 4.89/1.03    ~r1_tarski(sK1,sK0) | spl3_40),
% 4.89/1.03    inference(subsumption_resolution,[],[f3950,f213])).
% 4.89/1.03  fof(f3950,plain,(
% 4.89/1.03    sK0 != k5_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK0) | spl3_40),
% 4.89/1.03    inference(superposition,[],[f2284,f342])).
% 4.89/1.03  % (22693)Time limit reached!
% 4.89/1.03  % (22693)------------------------------
% 4.89/1.03  % (22693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.03  % (22882)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.89/1.03  % (22672)Termination reason: Time limit
% 4.89/1.03  % (22672)Termination phase: Saturation
% 4.89/1.03  
% 4.89/1.03  % (22672)Memory used [KB]: 11513
% 4.89/1.03  % (22672)Time elapsed: 0.600 s
% 4.89/1.03  % (22672)------------------------------
% 4.89/1.03  % (22672)------------------------------
% 4.89/1.03  fof(f342,plain,(
% 4.89/1.03    ( ! [X14,X15] : (k5_xboole_0(X14,X15) = k4_xboole_0(X14,X15) | ~r1_tarski(X15,X14)) )),
% 4.89/1.03    inference(superposition,[],[f69,f129])).
% 4.89/1.03  fof(f129,plain,(
% 4.89/1.03    ( ! [X6,X5] : (k3_xboole_0(X6,X5) = X5 | ~r1_tarski(X5,X6)) )),
% 4.89/1.03    inference(superposition,[],[f67,f50])).
% 4.89/1.03  fof(f50,plain,(
% 4.89/1.03    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.89/1.03    inference(cnf_transformation,[],[f1])).
% 4.89/1.03  fof(f1,axiom,(
% 4.89/1.03    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.89/1.03  fof(f69,plain,(
% 4.89/1.03    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.89/1.03    inference(cnf_transformation,[],[f6])).
% 4.89/1.03  fof(f6,axiom,(
% 4.89/1.03    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.89/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.89/1.03  % (22880)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.89/1.03  fof(f2284,plain,(
% 4.89/1.03    sK0 != k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | spl3_40),
% 4.89/1.03    inference(avatar_component_clause,[],[f2282])).
% 4.89/1.03  fof(f2282,plain,(
% 4.89/1.03    spl3_40 <=> sK0 = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 4.89/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 4.89/1.03  fof(f3778,plain,(
% 4.89/1.03    ~spl3_64 | ~spl3_5 | spl3_39),
% 4.89/1.03    inference(avatar_split_clause,[],[f3777,f2278,f118,f3761])).
% 4.89/1.03  fof(f2278,plain,(
% 4.89/1.03    spl3_39 <=> r1_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 4.89/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 4.89/1.03  fof(f3777,plain,(
% 4.89/1.03    ~r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | (~spl3_5 | spl3_39)),
% 4.89/1.03    inference(subsumption_resolution,[],[f3772,f120])).
% 4.89/1.03  fof(f3772,plain,(
% 4.89/1.03    ~r1_xboole_0(sK1,k5_xboole_0(sK0,sK1)) | ~r1_tarski(sK1,sK0) | spl3_39),
% 4.89/1.03    inference(superposition,[],[f2280,f342])).
% 4.89/1.03  fof(f2280,plain,(
% 4.89/1.03    ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | spl3_39),
% 4.89/1.03    inference(avatar_component_clause,[],[f2278])).
% 4.89/1.03  fof(f3765,plain,(
% 4.89/1.03    ~spl3_39 | ~spl3_40 | spl3_10),
% 4.89/1.03    inference(avatar_split_clause,[],[f3462,f245,f2282,f2278])).
% 4.89/1.03  fof(f245,plain,(
% 4.89/1.03    spl3_10 <=> sK0 = k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 4.89/1.03    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 4.89/1.03  fof(f3462,plain,(
% 4.89/1.03    sK0 != k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~r1_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | spl3_10),
% 4.89/1.03    inference(superposition,[],[f247,f2236])).
% 5.14/1.04  % (22693)Termination reason: Time limit
% 5.14/1.04  fof(f2236,plain,(
% 5.14/1.04    ( ! [X4,X3] : (k5_xboole_0(X3,X4) = k2_xboole_0(X3,X4) | ~r1_xboole_0(X3,X4)) )),
% 5.14/1.04    inference(backward_demodulation,[],[f199,f2159])).
% 5.14/1.04  fof(f2159,plain,(
% 5.14/1.04    ( ! [X7] : (k4_xboole_0(X7,k1_xboole_0) = X7) )),
% 5.14/1.04    inference(forward_demodulation,[],[f2131,f70])).
% 5.14/1.04  fof(f2131,plain,(
% 5.14/1.04    ( ! [X7] : (k5_xboole_0(X7,k1_xboole_0) = k4_xboole_0(X7,k1_xboole_0)) )),
% 5.14/1.04    inference(superposition,[],[f69,f2107])).
% 5.14/1.04  fof(f2107,plain,(
% 5.14/1.04    ( ! [X7] : (k1_xboole_0 = k3_xboole_0(X7,k1_xboole_0)) )),
% 5.14/1.04    inference(backward_demodulation,[],[f474,f1944])).
% 5.14/1.04  fof(f1944,plain,(
% 5.14/1.04    ( ! [X6] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X6)) )),
% 5.14/1.04    inference(backward_demodulation,[],[f139,f1925])).
% 5.14/1.04  fof(f1925,plain,(
% 5.14/1.04    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 5.14/1.04    inference(resolution,[],[f562,f122])).
% 5.14/1.04  fof(f122,plain,(
% 5.14/1.04    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 5.14/1.04    inference(superposition,[],[f66,f52])).
% 5.14/1.04  fof(f52,plain,(
% 5.14/1.04    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 5.14/1.04    inference(cnf_transformation,[],[f29])).
% 5.14/1.04  fof(f29,plain,(
% 5.14/1.04    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 5.14/1.04    inference(rectify,[],[f4])).
% 5.14/1.04  fof(f4,axiom,(
% 5.14/1.04    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 5.14/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 5.14/1.04  fof(f66,plain,(
% 5.14/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 5.14/1.04    inference(cnf_transformation,[],[f37])).
% 5.14/1.04  fof(f37,plain,(
% 5.14/1.04    ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1))),
% 5.14/1.04    inference(ennf_transformation,[],[f30])).
% 5.14/1.04  fof(f30,plain,(
% 5.14/1.04    ! [X0,X1] : (r1_xboole_0(X0,X1) => k3_xboole_0(X0,X1) = k1_xboole_0)),
% 5.14/1.04    inference(unused_predicate_definition_removal,[],[f3])).
% 5.14/1.04  fof(f3,axiom,(
% 5.14/1.04    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 5.14/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 5.14/1.04  fof(f562,plain,(
% 5.14/1.04    ( ! [X6] : (r1_xboole_0(k3_xboole_0(k1_xboole_0,X6),k3_xboole_0(k1_xboole_0,X6))) )),
% 5.14/1.04    inference(superposition,[],[f286,f148])).
% 5.14/1.04  fof(f148,plain,(
% 5.14/1.04    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 5.14/1.04    inference(superposition,[],[f48,f52])).
% 5.14/1.04  fof(f48,plain,(
% 5.14/1.04    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 5.14/1.04    inference(cnf_transformation,[],[f7])).
% 5.14/1.04  fof(f7,axiom,(
% 5.14/1.04    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 5.14/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 5.14/1.04  fof(f286,plain,(
% 5.14/1.04    ( ! [X10] : (r1_xboole_0(X10,k3_xboole_0(k1_xboole_0,X10))) )),
% 5.14/1.04    inference(superposition,[],[f203,f93])).
% 5.14/1.04  fof(f139,plain,(
% 5.14/1.04    ( ! [X6] : (k3_xboole_0(k1_xboole_0,X6) = k4_xboole_0(k1_xboole_0,X6)) )),
% 5.14/1.04    inference(superposition,[],[f69,f93])).
% 5.14/1.04  fof(f474,plain,(
% 5.14/1.04    ( ! [X7] : (k3_xboole_0(X7,k1_xboole_0) = k4_xboole_0(k1_xboole_0,X7)) )),
% 5.14/1.04    inference(superposition,[],[f137,f93])).
% 5.14/1.04  fof(f137,plain,(
% 5.14/1.04    ( ! [X6,X5] : (k4_xboole_0(X5,X6) = k5_xboole_0(X5,k3_xboole_0(X6,X5))) )),
% 5.14/1.04    inference(superposition,[],[f69,f50])).
% 5.14/1.04  fof(f199,plain,(
% 5.14/1.04    ( ! [X4,X3] : (k5_xboole_0(X3,X4) = k4_xboole_0(k2_xboole_0(X3,X4),k1_xboole_0) | ~r1_xboole_0(X3,X4)) )),
% 5.14/1.04    inference(superposition,[],[f68,f66])).
% 5.14/1.04  fof(f247,plain,(
% 5.14/1.04    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | spl3_10),
% 5.14/1.04    inference(avatar_component_clause,[],[f245])).
% 5.14/1.04  fof(f3746,plain,(
% 5.14/1.04    spl3_61 | ~spl3_5 | ~spl3_14),
% 5.14/1.04    inference(avatar_split_clause,[],[f3741,f324,f118,f3743])).
% 5.14/1.04  fof(f324,plain,(
% 5.14/1.04    spl3_14 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 5.14/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 5.14/1.04  fof(f3741,plain,(
% 5.14/1.04    r1_tarski(k5_xboole_0(sK0,sK1),sK0) | (~spl3_5 | ~spl3_14)),
% 5.14/1.04    inference(subsumption_resolution,[],[f3694,f120])).
% 5.14/1.04  fof(f3694,plain,(
% 5.14/1.04    r1_tarski(k5_xboole_0(sK0,sK1),sK0) | ~r1_tarski(sK1,sK0) | ~spl3_14),
% 5.14/1.04    inference(superposition,[],[f326,f342])).
% 5.14/1.04  fof(f326,plain,(
% 5.14/1.04    r1_tarski(k4_xboole_0(sK0,sK1),sK0) | ~spl3_14),
% 5.14/1.04    inference(avatar_component_clause,[],[f324])).
% 5.14/1.04  fof(f3470,plain,(
% 5.14/1.04    ~spl3_40 | ~spl3_2 | spl3_38),
% 5.14/1.04    inference(avatar_split_clause,[],[f3469,f2273,f83,f2282])).
% 5.14/1.04  fof(f83,plain,(
% 5.14/1.04    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 5.14/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 5.14/1.04  fof(f3469,plain,(
% 5.14/1.04    sK0 != k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | (~spl3_2 | spl3_38)),
% 5.14/1.04    inference(subsumption_resolution,[],[f3468,f85])).
% 5.14/1.04  fof(f85,plain,(
% 5.14/1.04    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 5.14/1.04    inference(avatar_component_clause,[],[f83])).
% 5.14/1.04  fof(f3468,plain,(
% 5.14/1.04    sK0 != k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_38),
% 5.14/1.04    inference(superposition,[],[f2275,f54])).
% 5.14/1.04  fof(f54,plain,(
% 5.14/1.04    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.14/1.04    inference(cnf_transformation,[],[f34])).
% 5.14/1.04  fof(f34,plain,(
% 5.14/1.04    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.14/1.04    inference(ennf_transformation,[],[f23])).
% 5.14/1.04  fof(f23,axiom,(
% 5.14/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 5.14/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 5.14/1.04  fof(f2275,plain,(
% 5.14/1.04    sK0 != k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) | spl3_38),
% 5.14/1.04    inference(avatar_component_clause,[],[f2273])).
% 5.14/1.04  fof(f3428,plain,(
% 5.14/1.04    spl3_14 | ~spl3_2 | ~spl3_13),
% 5.14/1.04    inference(avatar_split_clause,[],[f3427,f299,f83,f324])).
% 5.14/1.04  fof(f299,plain,(
% 5.14/1.04    spl3_13 <=> r1_tarski(k3_subset_1(sK0,sK1),sK0)),
% 5.14/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 5.14/1.04  fof(f3427,plain,(
% 5.14/1.04    r1_tarski(k4_xboole_0(sK0,sK1),sK0) | (~spl3_2 | ~spl3_13)),
% 5.14/1.04    inference(subsumption_resolution,[],[f3415,f85])).
% 5.14/1.04  fof(f3415,plain,(
% 5.14/1.04    r1_tarski(k4_xboole_0(sK0,sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl3_13),
% 5.14/1.04    inference(superposition,[],[f301,f54])).
% 5.14/1.04  fof(f301,plain,(
% 5.14/1.04    r1_tarski(k3_subset_1(sK0,sK1),sK0) | ~spl3_13),
% 5.14/1.04    inference(avatar_component_clause,[],[f299])).
% 5.14/1.04  fof(f3409,plain,(
% 5.14/1.04    ~spl3_10 | ~spl3_2 | spl3_8),
% 5.14/1.04    inference(avatar_split_clause,[],[f3408,f235,f83,f245])).
% 5.14/1.04  fof(f235,plain,(
% 5.14/1.04    spl3_8 <=> sK0 = k2_xboole_0(sK1,k3_subset_1(sK0,sK1))),
% 5.14/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 5.14/1.04  fof(f3408,plain,(
% 5.14/1.04    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | (~spl3_2 | spl3_8)),
% 5.14/1.04    inference(subsumption_resolution,[],[f3406,f85])).
% 5.14/1.04  fof(f3406,plain,(
% 5.14/1.04    sK0 != k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_8),
% 5.14/1.04    inference(superposition,[],[f237,f54])).
% 5.14/1.04  fof(f237,plain,(
% 5.14/1.04    sK0 != k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) | spl3_8),
% 5.14/1.04    inference(avatar_component_clause,[],[f235])).
% 5.14/1.04  fof(f3405,plain,(
% 5.14/1.04    spl3_11 | ~spl3_7),
% 5.14/1.04    inference(avatar_split_clause,[],[f3404,f231,f263])).
% 5.14/1.04  fof(f263,plain,(
% 5.14/1.04    spl3_11 <=> r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 5.14/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 5.14/1.04  fof(f231,plain,(
% 5.14/1.04    spl3_7 <=> m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 5.14/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 5.14/1.04  fof(f3404,plain,(
% 5.14/1.04    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_7),
% 5.14/1.04    inference(subsumption_resolution,[],[f3401,f65])).
% 5.14/1.04  fof(f65,plain,(
% 5.14/1.04    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 5.14/1.04    inference(cnf_transformation,[],[f25])).
% 5.14/1.04  fof(f25,axiom,(
% 5.14/1.04    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 5.14/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 5.14/1.04  fof(f3401,plain,(
% 5.14/1.04    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_7),
% 5.14/1.04    inference(resolution,[],[f232,f57])).
% 5.14/1.04  fof(f57,plain,(
% 5.14/1.04    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 5.14/1.04    inference(cnf_transformation,[],[f41])).
% 5.14/1.04  fof(f41,plain,(
% 5.14/1.04    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 5.14/1.04    inference(nnf_transformation,[],[f36])).
% 5.14/1.04  fof(f36,plain,(
% 5.14/1.04    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 5.14/1.04    inference(ennf_transformation,[],[f21])).
% 5.14/1.04  fof(f21,axiom,(
% 5.14/1.04    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 5.14/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 5.14/1.04  fof(f232,plain,(
% 5.14/1.04    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_7),
% 5.14/1.04    inference(avatar_component_clause,[],[f231])).
% 5.14/1.04  fof(f2628,plain,(
% 5.14/1.04    spl3_4 | ~spl3_2),
% 5.14/1.04    inference(avatar_split_clause,[],[f2627,f83,f109])).
% 5.14/1.04  fof(f109,plain,(
% 5.14/1.04    spl3_4 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 5.14/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 5.14/1.04  fof(f2627,plain,(
% 5.14/1.04    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_2),
% 5.14/1.04    inference(subsumption_resolution,[],[f2625,f65])).
% 5.14/1.04  fof(f2625,plain,(
% 5.14/1.04    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl3_2),
% 5.14/1.04    inference(resolution,[],[f85,f57])).
% 5.14/1.04  fof(f302,plain,(
% 5.14/1.04    spl3_13 | ~spl3_11),
% 5.14/1.04    inference(avatar_split_clause,[],[f295,f263,f299])).
% 5.14/1.04  fof(f295,plain,(
% 5.14/1.04    r1_tarski(k3_subset_1(sK0,sK1),sK0) | ~spl3_11),
% 5.14/1.04    inference(resolution,[],[f265,f76])).
% 5.14/1.04  fof(f76,plain,(
% 5.14/1.04    ( ! [X0,X3] : (~r2_hidden(X3,k1_zfmisc_1(X0)) | r1_tarski(X3,X0)) )),
% 5.14/1.04    inference(equality_resolution,[],[f61])).
% 5.14/1.04  fof(f61,plain,(
% 5.14/1.04    ( ! [X0,X3,X1] : (r1_tarski(X3,X0) | ~r2_hidden(X3,X1) | k1_zfmisc_1(X0) != X1) )),
% 5.14/1.04    inference(cnf_transformation,[],[f45])).
% 5.14/1.04  fof(f45,plain,(
% 5.14/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 5.14/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f43,f44])).
% 5.14/1.04  fof(f44,plain,(
% 5.14/1.04    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK2(X0,X1),X0) | ~r2_hidden(sK2(X0,X1),X1)) & (r1_tarski(sK2(X0,X1),X0) | r2_hidden(sK2(X0,X1),X1))))),
% 5.14/1.04    introduced(choice_axiom,[])).
% 5.14/1.04  fof(f43,plain,(
% 5.14/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 5.14/1.04    inference(rectify,[],[f42])).
% 5.14/1.04  fof(f42,plain,(
% 5.14/1.04    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 5.14/1.04    inference(nnf_transformation,[],[f19])).
% 5.14/1.04  fof(f19,axiom,(
% 5.14/1.04    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 5.14/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 5.14/1.04  fof(f265,plain,(
% 5.14/1.04    r2_hidden(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl3_11),
% 5.14/1.04    inference(avatar_component_clause,[],[f263])).
% 5.14/1.04  fof(f256,plain,(
% 5.14/1.04    ~spl3_2 | spl3_7),
% 5.14/1.04    inference(avatar_contradiction_clause,[],[f255])).
% 5.14/1.04  fof(f255,plain,(
% 5.14/1.04    $false | (~spl3_2 | spl3_7)),
% 5.14/1.04    inference(subsumption_resolution,[],[f250,f85])).
% 5.14/1.04  fof(f250,plain,(
% 5.14/1.04    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_7),
% 5.14/1.04    inference(resolution,[],[f233,f55])).
% 5.14/1.04  fof(f55,plain,(
% 5.14/1.04    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.14/1.04    inference(cnf_transformation,[],[f35])).
% 5.14/1.04  fof(f35,plain,(
% 5.14/1.04    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.14/1.04    inference(ennf_transformation,[],[f24])).
% 5.14/1.04  fof(f24,axiom,(
% 5.14/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 5.14/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 5.14/1.04  fof(f233,plain,(
% 5.14/1.04    ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl3_7),
% 5.14/1.04    inference(avatar_component_clause,[],[f231])).
% 5.14/1.04  fof(f238,plain,(
% 5.14/1.04    ~spl3_7 | ~spl3_8 | ~spl3_2 | spl3_3),
% 5.14/1.04    inference(avatar_split_clause,[],[f229,f89,f83,f235,f231])).
% 5.14/1.04  fof(f89,plain,(
% 5.14/1.04    spl3_3 <=> sK0 = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 5.14/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 5.14/1.04  fof(f229,plain,(
% 5.14/1.04    sK0 != k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl3_2 | spl3_3)),
% 5.14/1.04    inference(subsumption_resolution,[],[f227,f85])).
% 5.14/1.04  fof(f227,plain,(
% 5.14/1.04    sK0 != k2_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl3_3),
% 5.14/1.04    inference(superposition,[],[f91,f53])).
% 5.14/1.04  fof(f53,plain,(
% 5.14/1.04    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 5.14/1.04    inference(cnf_transformation,[],[f33])).
% 5.14/1.04  fof(f33,plain,(
% 5.14/1.04    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.14/1.04    inference(flattening,[],[f32])).
% 5.14/1.04  fof(f32,plain,(
% 5.14/1.04    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 5.14/1.04    inference(ennf_transformation,[],[f26])).
% 5.14/1.04  fof(f26,axiom,(
% 5.14/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 5.14/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 5.14/1.04  fof(f91,plain,(
% 5.14/1.04    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl3_3),
% 5.14/1.04    inference(avatar_component_clause,[],[f89])).
% 5.14/1.04  fof(f121,plain,(
% 5.14/1.04    spl3_5 | ~spl3_4),
% 5.14/1.04    inference(avatar_split_clause,[],[f115,f109,f118])).
% 5.14/1.04  fof(f115,plain,(
% 5.14/1.04    r1_tarski(sK1,sK0) | ~spl3_4),
% 5.14/1.04    inference(resolution,[],[f111,f76])).
% 5.14/1.04  fof(f111,plain,(
% 5.14/1.04    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl3_4),
% 5.14/1.04    inference(avatar_component_clause,[],[f109])).
% 5.14/1.04  fof(f92,plain,(
% 5.14/1.04    ~spl3_3 | spl3_1),
% 5.14/1.04    inference(avatar_split_clause,[],[f87,f78,f89])).
% 5.14/1.04  fof(f78,plain,(
% 5.14/1.04    spl3_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 5.14/1.04    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 5.14/1.04  fof(f87,plain,(
% 5.14/1.04    sK0 != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl3_1),
% 5.14/1.04    inference(backward_demodulation,[],[f80,f56])).
% 5.14/1.04  fof(f56,plain,(
% 5.14/1.04    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 5.14/1.04    inference(cnf_transformation,[],[f22])).
% 5.14/1.04  fof(f22,axiom,(
% 5.14/1.04    ! [X0] : k2_subset_1(X0) = X0),
% 5.14/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 5.14/1.04  fof(f80,plain,(
% 5.14/1.04    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) | spl3_1),
% 5.14/1.04    inference(avatar_component_clause,[],[f78])).
% 5.14/1.04  fof(f86,plain,(
% 5.14/1.04    spl3_2),
% 5.14/1.04    inference(avatar_split_clause,[],[f46,f83])).
% 5.14/1.04  fof(f46,plain,(
% 5.14/1.04    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 5.14/1.04    inference(cnf_transformation,[],[f40])).
% 5.14/1.04  fof(f40,plain,(
% 5.14/1.04    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 5.14/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f39])).
% 5.14/1.04  fof(f39,plain,(
% 5.14/1.04    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 5.14/1.04    introduced(choice_axiom,[])).
% 5.14/1.04  fof(f31,plain,(
% 5.14/1.04    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k3_subset_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 5.14/1.04    inference(ennf_transformation,[],[f28])).
% 5.14/1.04  fof(f28,negated_conjecture,(
% 5.14/1.04    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 5.14/1.04    inference(negated_conjecture,[],[f27])).
% 5.14/1.04  fof(f27,conjecture,(
% 5.14/1.04    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k3_subset_1(X0,X1)))),
% 5.14/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).
% 5.14/1.04  fof(f81,plain,(
% 5.14/1.04    ~spl3_1),
% 5.14/1.04    inference(avatar_split_clause,[],[f47,f78])).
% 5.14/1.04  fof(f47,plain,(
% 5.14/1.04    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k3_subset_1(sK0,sK1))),
% 5.14/1.04    inference(cnf_transformation,[],[f40])).
% 5.14/1.04  % SZS output end Proof for theBenchmark
% 5.14/1.04  % (22733)------------------------------
% 5.14/1.04  % (22733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.14/1.04  % (22733)Termination reason: Refutation
% 5.14/1.04  
% 5.14/1.04  % (22733)Memory used [KB]: 9722
% 5.14/1.04  % (22733)Time elapsed: 0.426 s
% 5.14/1.04  % (22733)------------------------------
% 5.14/1.04  % (22733)------------------------------
% 5.14/1.04  
% 5.14/1.04  % (22693)Memory used [KB]: 9083
% 5.14/1.04  % (22693)Time elapsed: 0.630 s
% 5.14/1.04  % (22693)------------------------------
% 5.14/1.04  % (22693)------------------------------
% 5.14/1.04  % (22664)Success in time 0.686 s
%------------------------------------------------------------------------------
