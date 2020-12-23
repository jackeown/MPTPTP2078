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
% DateTime   : Thu Dec  3 12:45:00 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 396 expanded)
%              Number of leaves         :   43 ( 158 expanded)
%              Depth                    :   10
%              Number of atoms          :  434 ( 908 expanded)
%              Number of equality atoms :   80 ( 204 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4926,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f293,f298,f307,f401,f432,f447,f474,f480,f493,f502,f523,f532,f550,f586,f625,f646,f1100,f1138,f1198,f2632,f2637,f4755,f4923])).

fof(f4923,plain,
    ( ~ spl5_225
    | spl5_260 ),
    inference(avatar_contradiction_clause,[],[f4922])).

fof(f4922,plain,
    ( $false
    | ~ spl5_225
    | spl5_260 ),
    inference(subsumption_resolution,[],[f4921,f78])).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f40,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f4921,plain,
    ( ~ r1_tarski(k1_xboole_0,sK1)
    | ~ spl5_225
    | spl5_260 ),
    inference(forward_demodulation,[],[f4920,f75])).

fof(f75,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f42,f39])).

fof(f39,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f4920,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)),sK1)
    | ~ spl5_225
    | spl5_260 ),
    inference(forward_demodulation,[],[f4909,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f4909,plain,
    ( ~ r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK3),sK1)
    | ~ spl5_225
    | spl5_260 ),
    inference(unit_resulting_resolution,[],[f4754,f2970])).

fof(f2970,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k4_xboole_0(X1,sK3),sK1)
        | r1_tarski(X1,sK1) )
    | ~ spl5_225 ),
    inference(superposition,[],[f216,f2636])).

fof(f2636,plain,
    ( sK1 = k2_xboole_0(sK1,sK3)
    | ~ spl5_225 ),
    inference(avatar_component_clause,[],[f2634])).

fof(f2634,plain,
    ( spl5_225
  <=> sK1 = k2_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_225])])).

fof(f216,plain,(
    ! [X4,X2,X3] :
      ( r1_tarski(X4,k2_xboole_0(X3,X2))
      | ~ r1_tarski(k4_xboole_0(X4,X2),X3) ) ),
    inference(superposition,[],[f57,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f4754,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK1)
    | spl5_260 ),
    inference(avatar_component_clause,[],[f4752])).

fof(f4752,plain,
    ( spl5_260
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_260])])).

fof(f4755,plain,
    ( ~ spl5_260
    | spl5_115
    | ~ spl5_224 ),
    inference(avatar_split_clause,[],[f4737,f2629,f1135,f4752])).

fof(f1135,plain,
    ( spl5_115
  <=> r1_tarski(k2_xboole_0(sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).

fof(f2629,plain,
    ( spl5_224
  <=> sK1 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_224])])).

fof(f4737,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK1)
    | spl5_115
    | ~ spl5_224 ),
    inference(unit_resulting_resolution,[],[f1137,f2955])).

fof(f2955,plain,
    ( ! [X1] :
        ( ~ r1_tarski(k4_xboole_0(X1,sK2),sK1)
        | r1_tarski(X1,sK1) )
    | ~ spl5_224 ),
    inference(superposition,[],[f216,f2631])).

fof(f2631,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl5_224 ),
    inference(avatar_component_clause,[],[f2629])).

fof(f1137,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),sK1)
    | spl5_115 ),
    inference(avatar_component_clause,[],[f1135])).

fof(f2637,plain,
    ( spl5_225
    | ~ spl5_49 ),
    inference(avatar_split_clause,[],[f2627,f635,f2634])).

fof(f635,plain,
    ( spl5_49
  <=> k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f2627,plain,
    ( sK1 = k2_xboole_0(sK1,sK3)
    | ~ spl5_49 ),
    inference(backward_demodulation,[],[f637,f2625])).

fof(f2625,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(forward_demodulation,[],[f2596,f137])).

fof(f137,plain,(
    ! [X4] : k2_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f132,f39])).

fof(f132,plain,(
    ! [X4] : k2_xboole_0(X4,X4) = k2_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f43,f75])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2596,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f563,f76])).

fof(f76,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f42,f41])).

fof(f563,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4))) ),
    inference(superposition,[],[f43,f56])).

fof(f637,plain,
    ( k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f635])).

fof(f2632,plain,
    ( spl5_224
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f2626,f614,f2629])).

fof(f614,plain,
    ( spl5_47
  <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f2626,plain,
    ( sK1 = k2_xboole_0(sK1,sK2)
    | ~ spl5_47 ),
    inference(backward_demodulation,[],[f616,f2625])).

fof(f616,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f614])).

fof(f1198,plain,
    ( spl5_30
    | ~ spl5_110 ),
    inference(avatar_contradiction_clause,[],[f1197])).

fof(f1197,plain,
    ( $false
    | spl5_30
    | ~ spl5_110 ),
    inference(subsumption_resolution,[],[f1159,f564])).

fof(f564,plain,(
    ! [X6,X7,X5] : r1_tarski(k4_xboole_0(X5,k2_xboole_0(X6,X7)),k4_xboole_0(X5,X6)) ),
    inference(superposition,[],[f40,f56])).

fof(f1159,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2))
    | spl5_30
    | ~ spl5_110 ),
    inference(backward_demodulation,[],[f400,f1099])).

fof(f1099,plain,
    ( k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3)
    | ~ spl5_110 ),
    inference(avatar_component_clause,[],[f1097])).

fof(f1097,plain,
    ( spl5_110
  <=> k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f400,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f398])).

fof(f398,plain,
    ( spl5_30
  <=> r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f1138,plain,
    ( ~ spl5_115
    | ~ spl5_2
    | ~ spl5_3
    | spl5_37 ),
    inference(avatar_split_clause,[],[f1133,f444,f71,f66,f1135])).

fof(f66,plain,
    ( spl5_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f71,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f444,plain,
    ( spl5_37
  <=> r1_tarski(k4_subset_1(sK1,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f1133,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),sK1)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_37 ),
    inference(subsumption_resolution,[],[f1132,f73])).

fof(f73,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f1132,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | ~ spl5_2
    | spl5_37 ),
    inference(subsumption_resolution,[],[f841,f68])).

fof(f68,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f841,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK1))
    | spl5_37 ),
    inference(superposition,[],[f446,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f446,plain,
    ( ~ r1_tarski(k4_subset_1(sK1,sK2,sK3),sK1)
    | spl5_37 ),
    inference(avatar_component_clause,[],[f444])).

fof(f1100,plain,
    ( spl5_110
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f791,f71,f66,f1097])).

fof(f791,plain,
    ( k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3)
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f73,f68,f58])).

fof(f646,plain,
    ( spl5_49
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f633,f583,f635])).

fof(f583,plain,
    ( spl5_46
  <=> k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f633,plain,
    ( k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl5_46 ),
    inference(superposition,[],[f41,f585])).

fof(f585,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(sK1,sK3)
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f583])).

fof(f625,plain,
    ( spl5_47
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f612,f547,f614])).

fof(f547,plain,
    ( spl5_45
  <=> k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f612,plain,
    ( k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl5_45 ),
    inference(superposition,[],[f41,f549])).

fof(f549,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f547])).

fof(f586,plain,
    ( spl5_46
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f581,f519,f583])).

fof(f519,plain,
    ( spl5_44
  <=> sK3 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f581,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(sK1,sK3)
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f580,f41])).

fof(f580,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(sK3,sK1)
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f579,f43])).

fof(f579,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(sK3,k4_xboole_0(sK1,sK3))
    | ~ spl5_44 ),
    inference(forward_demodulation,[],[f577,f41])).

fof(f577,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK3)
    | ~ spl5_44 ),
    inference(superposition,[],[f43,f521])).

fof(f521,plain,
    ( sK3 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f519])).

fof(f550,plain,
    ( spl5_45
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f545,f489,f547])).

fof(f489,plain,
    ( spl5_42
  <=> sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f545,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK1,sK2)
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f544,f41])).

fof(f544,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK2,sK1)
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f543,f43])).

fof(f543,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))
    | ~ spl5_42 ),
    inference(forward_demodulation,[],[f541,f41])).

fof(f541,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2)
    | ~ spl5_42 ),
    inference(superposition,[],[f43,f491])).

fof(f491,plain,
    ( sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f489])).

fof(f532,plain,(
    spl5_43 ),
    inference(avatar_contradiction_clause,[],[f531])).

fof(f531,plain,
    ( $false
    | spl5_43 ),
    inference(subsumption_resolution,[],[f530,f38])).

fof(f38,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f530,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | spl5_43 ),
    inference(subsumption_resolution,[],[f525,f180])).

fof(f180,plain,(
    ! [X0,X1] : r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f40,f59,f51])).

fof(f51,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK4(X0,X1),X0)
            | ~ r2_hidden(sK4(X0,X1),X1) )
          & ( r1_tarski(sK4(X0,X1),X0)
            | r2_hidden(sK4(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK4(X0,X1),X0)
          | ~ r2_hidden(sK4(X0,X1),X1) )
        & ( r1_tarski(sK4(X0,X1),X0)
          | r2_hidden(sK4(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
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
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f59,plain,(
    ! [X0] : sP0(X0,k1_zfmisc_1(X0)) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f8,f24])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f525,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK3),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | spl5_43 ),
    inference(resolution,[],[f517,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f517,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK3),k1_zfmisc_1(sK1))
    | spl5_43 ),
    inference(avatar_component_clause,[],[f515])).

fof(f515,plain,
    ( spl5_43
  <=> m1_subset_1(k4_xboole_0(sK1,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f523,plain,
    ( ~ spl5_43
    | spl5_44
    | ~ spl5_40 ),
    inference(avatar_split_clause,[],[f513,f477,f519,f515])).

fof(f477,plain,
    ( spl5_40
  <=> sK3 = k3_subset_1(sK1,k4_xboole_0(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f513,plain,
    ( sK3 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl5_40 ),
    inference(superposition,[],[f48,f479])).

fof(f479,plain,
    ( sK3 = k3_subset_1(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f477])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f502,plain,(
    spl5_41 ),
    inference(avatar_contradiction_clause,[],[f501])).

fof(f501,plain,
    ( $false
    | spl5_41 ),
    inference(subsumption_resolution,[],[f500,f38])).

fof(f500,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK1))
    | spl5_41 ),
    inference(subsumption_resolution,[],[f495,f180])).

fof(f495,plain,
    ( ~ r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | spl5_41 ),
    inference(resolution,[],[f487,f45])).

fof(f487,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))
    | spl5_41 ),
    inference(avatar_component_clause,[],[f485])).

fof(f485,plain,
    ( spl5_41
  <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f493,plain,
    ( ~ spl5_41
    | spl5_42
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f483,f471,f489,f485])).

fof(f471,plain,
    ( spl5_39
  <=> sK2 = k3_subset_1(sK1,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f483,plain,
    ( sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))
    | ~ spl5_39 ),
    inference(superposition,[],[f48,f473])).

fof(f473,plain,
    ( sK2 = k3_subset_1(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f471])).

fof(f480,plain,
    ( spl5_40
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f475,f295,f66,f477])).

fof(f295,plain,
    ( spl5_13
  <=> k4_xboole_0(sK1,sK3) = k3_subset_1(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f475,plain,
    ( sK3 = k3_subset_1(sK1,k4_xboole_0(sK1,sK3))
    | ~ spl5_2
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f457,f297])).

fof(f297,plain,
    ( k4_xboole_0(sK1,sK3) = k3_subset_1(sK1,sK3)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f295])).

fof(f457,plain,
    ( sK3 = k3_subset_1(sK1,k3_subset_1(sK1,sK3))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f68,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f474,plain,
    ( spl5_39
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f469,f290,f71,f471])).

fof(f290,plain,
    ( spl5_12
  <=> k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f469,plain,
    ( sK2 = k3_subset_1(sK1,k4_xboole_0(sK1,sK2))
    | ~ spl5_3
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f458,f292])).

fof(f292,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f290])).

fof(f458,plain,
    ( sK2 = k3_subset_1(sK1,k3_subset_1(sK1,sK2))
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f73,f49])).

fof(f447,plain,
    ( ~ spl5_37
    | spl5_35 ),
    inference(avatar_split_clause,[],[f433,f427,f444])).

fof(f427,plain,
    ( spl5_35
  <=> r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f433,plain,
    ( ~ r1_tarski(k4_subset_1(sK1,sK2,sK3),sK1)
    | spl5_35 ),
    inference(unit_resulting_resolution,[],[f59,f429,f51])).

fof(f429,plain,
    ( ~ r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_35 ),
    inference(avatar_component_clause,[],[f427])).

fof(f432,plain,
    ( ~ spl5_35
    | spl5_14 ),
    inference(avatar_split_clause,[],[f431,f300,f427])).

fof(f300,plain,
    ( spl5_14
  <=> m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f431,plain,
    ( ~ r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_14 ),
    inference(subsumption_resolution,[],[f423,f38])).

fof(f423,plain,
    ( ~ r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | v1_xboole_0(k1_zfmisc_1(sK1))
    | spl5_14 ),
    inference(resolution,[],[f302,f45])).

fof(f302,plain,
    ( ~ m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f300])).

fof(f401,plain,
    ( ~ spl5_30
    | ~ spl5_12
    | spl5_15 ),
    inference(avatar_split_clause,[],[f392,f304,f290,f398])).

fof(f304,plain,
    ( spl5_15
  <=> r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f392,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))
    | ~ spl5_12
    | spl5_15 ),
    inference(backward_demodulation,[],[f306,f292])).

fof(f306,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f304])).

fof(f307,plain,
    ( ~ spl5_14
    | ~ spl5_15
    | spl5_1 ),
    inference(avatar_split_clause,[],[f270,f61,f304,f300])).

fof(f61,plain,
    ( spl5_1
  <=> r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f270,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | ~ m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))
    | spl5_1 ),
    inference(superposition,[],[f63,f48])).

fof(f63,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f298,plain,
    ( spl5_13
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f266,f66,f295])).

fof(f266,plain,
    ( k4_xboole_0(sK1,sK3) = k3_subset_1(sK1,sK3)
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f68,f48])).

fof(f293,plain,
    ( spl5_12
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f267,f71,f290])).

fof(f267,plain,
    ( k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)
    | ~ spl5_3 ),
    inference(unit_resulting_resolution,[],[f73,f48])).

fof(f74,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f35,f71])).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(sK1))
    & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f27,f26])).

fof(f26,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2))
          & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2))
        & m1_subset_1(X2,k1_zfmisc_1(sK1)) )
   => ( ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))
      & m1_subset_1(sK3,k1_zfmisc_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f69,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f36,f66])).

fof(f36,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f37,f61])).

fof(f37,plain,(
    ~ r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:37:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (21445)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  % (21431)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (21431)Refutation not found, incomplete strategy% (21431)------------------------------
% 0.21/0.48  % (21431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21431)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21431)Memory used [KB]: 10618
% 0.21/0.48  % (21431)Time elapsed: 0.062 s
% 0.21/0.48  % (21431)------------------------------
% 0.21/0.48  % (21431)------------------------------
% 0.21/0.48  % (21439)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (21439)Refutation not found, incomplete strategy% (21439)------------------------------
% 0.21/0.48  % (21439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21439)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21439)Memory used [KB]: 10618
% 0.21/0.48  % (21439)Time elapsed: 0.071 s
% 0.21/0.48  % (21439)------------------------------
% 0.21/0.48  % (21439)------------------------------
% 0.21/0.49  % (21438)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (21438)Refutation not found, incomplete strategy% (21438)------------------------------
% 0.21/0.49  % (21438)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21438)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (21438)Memory used [KB]: 6140
% 0.21/0.49  % (21438)Time elapsed: 0.051 s
% 0.21/0.49  % (21438)------------------------------
% 0.21/0.49  % (21438)------------------------------
% 0.21/0.49  % (21442)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (21433)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (21441)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (21430)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (21441)Refutation not found, incomplete strategy% (21441)------------------------------
% 0.21/0.50  % (21441)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21441)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21441)Memory used [KB]: 1663
% 0.21/0.50  % (21441)Time elapsed: 0.090 s
% 0.21/0.50  % (21441)------------------------------
% 0.21/0.50  % (21441)------------------------------
% 0.21/0.50  % (21434)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (21432)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (21444)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (21429)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (21446)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (21447)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (21443)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.51  % (21448)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (21440)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (21429)Refutation not found, incomplete strategy% (21429)------------------------------
% 0.21/0.51  % (21429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21429)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21429)Memory used [KB]: 10618
% 0.21/0.51  % (21429)Time elapsed: 0.092 s
% 0.21/0.51  % (21429)------------------------------
% 0.21/0.51  % (21429)------------------------------
% 0.21/0.51  % (21448)Refutation not found, incomplete strategy% (21448)------------------------------
% 0.21/0.51  % (21448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21448)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21448)Memory used [KB]: 10490
% 0.21/0.51  % (21448)Time elapsed: 0.095 s
% 0.21/0.51  % (21448)------------------------------
% 0.21/0.51  % (21448)------------------------------
% 0.21/0.51  % (21440)Refutation not found, incomplete strategy% (21440)------------------------------
% 0.21/0.51  % (21440)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21440)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21440)Memory used [KB]: 6140
% 0.21/0.51  % (21440)Time elapsed: 0.098 s
% 0.21/0.51  % (21440)------------------------------
% 0.21/0.51  % (21440)------------------------------
% 0.21/0.51  % (21443)Refutation not found, incomplete strategy% (21443)------------------------------
% 0.21/0.51  % (21443)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21443)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21443)Memory used [KB]: 6140
% 0.21/0.51  % (21443)Time elapsed: 0.095 s
% 0.21/0.51  % (21443)------------------------------
% 0.21/0.51  % (21443)------------------------------
% 0.21/0.51  % (21435)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (21437)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (21436)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (21428)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (21428)Refutation not found, incomplete strategy% (21428)------------------------------
% 0.21/0.52  % (21428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21428)Memory used [KB]: 6140
% 0.21/0.52  % (21428)Time elapsed: 0.112 s
% 0.21/0.52  % (21428)------------------------------
% 0.21/0.52  % (21428)------------------------------
% 1.79/0.64  % (21444)Refutation found. Thanks to Tanya!
% 1.79/0.64  % SZS status Theorem for theBenchmark
% 1.79/0.64  % SZS output start Proof for theBenchmark
% 1.79/0.64  fof(f4926,plain,(
% 1.79/0.64    $false),
% 1.79/0.64    inference(avatar_sat_refutation,[],[f64,f69,f74,f293,f298,f307,f401,f432,f447,f474,f480,f493,f502,f523,f532,f550,f586,f625,f646,f1100,f1138,f1198,f2632,f2637,f4755,f4923])).
% 1.79/0.64  fof(f4923,plain,(
% 1.79/0.64    ~spl5_225 | spl5_260),
% 1.79/0.64    inference(avatar_contradiction_clause,[],[f4922])).
% 1.79/0.64  fof(f4922,plain,(
% 1.79/0.64    $false | (~spl5_225 | spl5_260)),
% 1.79/0.64    inference(subsumption_resolution,[],[f4921,f78])).
% 1.79/0.64  fof(f78,plain,(
% 1.79/0.64    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.79/0.64    inference(superposition,[],[f40,f42])).
% 1.79/0.64  fof(f42,plain,(
% 1.79/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 1.79/0.64    inference(cnf_transformation,[],[f7])).
% 1.79/0.64  fof(f7,axiom,(
% 1.79/0.64    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 1.79/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.32/0.64  fof(f40,plain,(
% 2.32/0.64    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.32/0.64    inference(cnf_transformation,[],[f3])).
% 2.32/0.64  fof(f3,axiom,(
% 2.32/0.64    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.32/0.64  fof(f4921,plain,(
% 2.32/0.64    ~r1_tarski(k1_xboole_0,sK1) | (~spl5_225 | spl5_260)),
% 2.32/0.64    inference(forward_demodulation,[],[f4920,f75])).
% 2.32/0.64  fof(f75,plain,(
% 2.32/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 2.32/0.64    inference(superposition,[],[f42,f39])).
% 2.32/0.64  fof(f39,plain,(
% 2.32/0.64    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.32/0.64    inference(cnf_transformation,[],[f16])).
% 2.32/0.64  fof(f16,plain,(
% 2.32/0.64    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.32/0.64    inference(rectify,[],[f2])).
% 2.32/0.64  fof(f2,axiom,(
% 2.32/0.64    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.32/0.64  fof(f4920,plain,(
% 2.32/0.64    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),k2_xboole_0(sK2,sK3)),sK1) | (~spl5_225 | spl5_260)),
% 2.32/0.64    inference(forward_demodulation,[],[f4909,f56])).
% 2.32/0.64  fof(f56,plain,(
% 2.32/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.32/0.64    inference(cnf_transformation,[],[f5])).
% 2.32/0.64  fof(f5,axiom,(
% 2.32/0.64    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.32/0.64  fof(f4909,plain,(
% 2.32/0.64    ~r1_tarski(k4_xboole_0(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK3),sK1) | (~spl5_225 | spl5_260)),
% 2.32/0.64    inference(unit_resulting_resolution,[],[f4754,f2970])).
% 2.32/0.64  fof(f2970,plain,(
% 2.32/0.64    ( ! [X1] : (~r1_tarski(k4_xboole_0(X1,sK3),sK1) | r1_tarski(X1,sK1)) ) | ~spl5_225),
% 2.32/0.64    inference(superposition,[],[f216,f2636])).
% 2.32/0.64  fof(f2636,plain,(
% 2.32/0.64    sK1 = k2_xboole_0(sK1,sK3) | ~spl5_225),
% 2.32/0.64    inference(avatar_component_clause,[],[f2634])).
% 2.32/0.64  fof(f2634,plain,(
% 2.32/0.64    spl5_225 <=> sK1 = k2_xboole_0(sK1,sK3)),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_225])])).
% 2.32/0.64  fof(f216,plain,(
% 2.32/0.64    ( ! [X4,X2,X3] : (r1_tarski(X4,k2_xboole_0(X3,X2)) | ~r1_tarski(k4_xboole_0(X4,X2),X3)) )),
% 2.32/0.64    inference(superposition,[],[f57,f41])).
% 2.32/0.64  fof(f41,plain,(
% 2.32/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.32/0.64    inference(cnf_transformation,[],[f1])).
% 2.32/0.64  fof(f1,axiom,(
% 2.32/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.32/0.64  fof(f57,plain,(
% 2.32/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 2.32/0.64    inference(cnf_transformation,[],[f21])).
% 2.32/0.64  fof(f21,plain,(
% 2.32/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 2.32/0.64    inference(ennf_transformation,[],[f6])).
% 2.32/0.64  fof(f6,axiom,(
% 2.32/0.64    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 2.32/0.64  fof(f4754,plain,(
% 2.32/0.64    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK1) | spl5_260),
% 2.32/0.64    inference(avatar_component_clause,[],[f4752])).
% 2.32/0.64  fof(f4752,plain,(
% 2.32/0.64    spl5_260 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK1)),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_260])])).
% 2.32/0.64  fof(f4755,plain,(
% 2.32/0.64    ~spl5_260 | spl5_115 | ~spl5_224),
% 2.32/0.64    inference(avatar_split_clause,[],[f4737,f2629,f1135,f4752])).
% 2.32/0.64  fof(f1135,plain,(
% 2.32/0.64    spl5_115 <=> r1_tarski(k2_xboole_0(sK2,sK3),sK1)),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_115])])).
% 2.32/0.64  fof(f2629,plain,(
% 2.32/0.64    spl5_224 <=> sK1 = k2_xboole_0(sK1,sK2)),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_224])])).
% 2.32/0.64  fof(f4737,plain,(
% 2.32/0.64    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK2,sK3),sK2),sK1) | (spl5_115 | ~spl5_224)),
% 2.32/0.64    inference(unit_resulting_resolution,[],[f1137,f2955])).
% 2.32/0.64  fof(f2955,plain,(
% 2.32/0.64    ( ! [X1] : (~r1_tarski(k4_xboole_0(X1,sK2),sK1) | r1_tarski(X1,sK1)) ) | ~spl5_224),
% 2.32/0.64    inference(superposition,[],[f216,f2631])).
% 2.32/0.64  fof(f2631,plain,(
% 2.32/0.64    sK1 = k2_xboole_0(sK1,sK2) | ~spl5_224),
% 2.32/0.64    inference(avatar_component_clause,[],[f2629])).
% 2.32/0.64  fof(f1137,plain,(
% 2.32/0.64    ~r1_tarski(k2_xboole_0(sK2,sK3),sK1) | spl5_115),
% 2.32/0.64    inference(avatar_component_clause,[],[f1135])).
% 2.32/0.64  fof(f2637,plain,(
% 2.32/0.64    spl5_225 | ~spl5_49),
% 2.32/0.64    inference(avatar_split_clause,[],[f2627,f635,f2634])).
% 2.32/0.64  fof(f635,plain,(
% 2.32/0.64    spl5_49 <=> k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 2.32/0.64  fof(f2627,plain,(
% 2.32/0.64    sK1 = k2_xboole_0(sK1,sK3) | ~spl5_49),
% 2.32/0.64    inference(backward_demodulation,[],[f637,f2625])).
% 2.32/0.64  fof(f2625,plain,(
% 2.32/0.64    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 2.32/0.64    inference(forward_demodulation,[],[f2596,f137])).
% 2.32/0.64  fof(f137,plain,(
% 2.32/0.64    ( ! [X4] : (k2_xboole_0(X4,k1_xboole_0) = X4) )),
% 2.32/0.64    inference(forward_demodulation,[],[f132,f39])).
% 2.32/0.64  fof(f132,plain,(
% 2.32/0.64    ( ! [X4] : (k2_xboole_0(X4,X4) = k2_xboole_0(X4,k1_xboole_0)) )),
% 2.32/0.64    inference(superposition,[],[f43,f75])).
% 2.32/0.64  fof(f43,plain,(
% 2.32/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.32/0.64    inference(cnf_transformation,[],[f4])).
% 2.32/0.64  fof(f4,axiom,(
% 2.32/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.32/0.64  fof(f2596,plain,(
% 2.32/0.64    ( ! [X2,X3] : (k2_xboole_0(X2,k1_xboole_0) = k2_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 2.32/0.64    inference(superposition,[],[f563,f76])).
% 2.32/0.64  fof(f76,plain,(
% 2.32/0.64    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 2.32/0.64    inference(superposition,[],[f42,f41])).
% 2.32/0.64  fof(f563,plain,(
% 2.32/0.64    ( ! [X4,X2,X3] : (k2_xboole_0(X4,k4_xboole_0(X2,X3)) = k2_xboole_0(X4,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) )),
% 2.32/0.64    inference(superposition,[],[f43,f56])).
% 2.32/0.64  fof(f637,plain,(
% 2.32/0.64    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl5_49),
% 2.32/0.64    inference(avatar_component_clause,[],[f635])).
% 2.32/0.64  fof(f2632,plain,(
% 2.32/0.64    spl5_224 | ~spl5_47),
% 2.32/0.64    inference(avatar_split_clause,[],[f2626,f614,f2629])).
% 2.32/0.64  fof(f614,plain,(
% 2.32/0.64    spl5_47 <=> k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 2.32/0.64  fof(f2626,plain,(
% 2.32/0.64    sK1 = k2_xboole_0(sK1,sK2) | ~spl5_47),
% 2.32/0.64    inference(backward_demodulation,[],[f616,f2625])).
% 2.32/0.64  fof(f616,plain,(
% 2.32/0.64    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl5_47),
% 2.32/0.64    inference(avatar_component_clause,[],[f614])).
% 2.32/0.64  fof(f1198,plain,(
% 2.32/0.64    spl5_30 | ~spl5_110),
% 2.32/0.64    inference(avatar_contradiction_clause,[],[f1197])).
% 2.32/0.64  fof(f1197,plain,(
% 2.32/0.64    $false | (spl5_30 | ~spl5_110)),
% 2.32/0.64    inference(subsumption_resolution,[],[f1159,f564])).
% 2.32/0.64  fof(f564,plain,(
% 2.32/0.64    ( ! [X6,X7,X5] : (r1_tarski(k4_xboole_0(X5,k2_xboole_0(X6,X7)),k4_xboole_0(X5,X6))) )),
% 2.32/0.64    inference(superposition,[],[f40,f56])).
% 2.32/0.64  fof(f1159,plain,(
% 2.32/0.64    ~r1_tarski(k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)),k4_xboole_0(sK1,sK2)) | (spl5_30 | ~spl5_110)),
% 2.32/0.64    inference(backward_demodulation,[],[f400,f1099])).
% 2.32/0.64  fof(f1099,plain,(
% 2.32/0.64    k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) | ~spl5_110),
% 2.32/0.64    inference(avatar_component_clause,[],[f1097])).
% 2.32/0.64  fof(f1097,plain,(
% 2.32/0.64    spl5_110 <=> k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3)),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).
% 2.32/0.64  fof(f400,plain,(
% 2.32/0.64    ~r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2)) | spl5_30),
% 2.32/0.64    inference(avatar_component_clause,[],[f398])).
% 2.32/0.64  fof(f398,plain,(
% 2.32/0.64    spl5_30 <=> r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 2.32/0.64  fof(f1138,plain,(
% 2.32/0.64    ~spl5_115 | ~spl5_2 | ~spl5_3 | spl5_37),
% 2.32/0.64    inference(avatar_split_clause,[],[f1133,f444,f71,f66,f1135])).
% 2.32/0.64  fof(f66,plain,(
% 2.32/0.64    spl5_2 <=> m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.32/0.64  fof(f71,plain,(
% 2.32/0.64    spl5_3 <=> m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.32/0.64  fof(f444,plain,(
% 2.32/0.64    spl5_37 <=> r1_tarski(k4_subset_1(sK1,sK2,sK3),sK1)),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 2.32/0.64  fof(f1133,plain,(
% 2.32/0.64    ~r1_tarski(k2_xboole_0(sK2,sK3),sK1) | (~spl5_2 | ~spl5_3 | spl5_37)),
% 2.32/0.64    inference(subsumption_resolution,[],[f1132,f73])).
% 2.32/0.64  fof(f73,plain,(
% 2.32/0.64    m1_subset_1(sK2,k1_zfmisc_1(sK1)) | ~spl5_3),
% 2.32/0.64    inference(avatar_component_clause,[],[f71])).
% 2.32/0.64  fof(f1132,plain,(
% 2.32/0.64    ~r1_tarski(k2_xboole_0(sK2,sK3),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | (~spl5_2 | spl5_37)),
% 2.32/0.64    inference(subsumption_resolution,[],[f841,f68])).
% 2.32/0.64  fof(f68,plain,(
% 2.32/0.64    m1_subset_1(sK3,k1_zfmisc_1(sK1)) | ~spl5_2),
% 2.32/0.64    inference(avatar_component_clause,[],[f66])).
% 2.32/0.64  fof(f841,plain,(
% 2.32/0.64    ~r1_tarski(k2_xboole_0(sK2,sK3),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK1)) | spl5_37),
% 2.32/0.64    inference(superposition,[],[f446,f58])).
% 2.32/0.64  fof(f58,plain,(
% 2.32/0.64    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.32/0.64    inference(cnf_transformation,[],[f23])).
% 2.32/0.64  fof(f23,plain,(
% 2.32/0.64    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.32/0.64    inference(flattening,[],[f22])).
% 2.32/0.64  fof(f22,plain,(
% 2.32/0.64    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.32/0.64    inference(ennf_transformation,[],[f13])).
% 2.32/0.64  fof(f13,axiom,(
% 2.32/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.32/0.64  fof(f446,plain,(
% 2.32/0.64    ~r1_tarski(k4_subset_1(sK1,sK2,sK3),sK1) | spl5_37),
% 2.32/0.64    inference(avatar_component_clause,[],[f444])).
% 2.32/0.64  fof(f1100,plain,(
% 2.32/0.64    spl5_110 | ~spl5_2 | ~spl5_3),
% 2.32/0.64    inference(avatar_split_clause,[],[f791,f71,f66,f1097])).
% 2.32/0.64  fof(f791,plain,(
% 2.32/0.64    k4_subset_1(sK1,sK2,sK3) = k2_xboole_0(sK2,sK3) | (~spl5_2 | ~spl5_3)),
% 2.32/0.64    inference(unit_resulting_resolution,[],[f73,f68,f58])).
% 2.32/0.64  fof(f646,plain,(
% 2.32/0.64    spl5_49 | ~spl5_46),
% 2.32/0.64    inference(avatar_split_clause,[],[f633,f583,f635])).
% 2.32/0.64  fof(f583,plain,(
% 2.32/0.64    spl5_46 <=> k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(sK1,sK3)),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 2.32/0.64  fof(f633,plain,(
% 2.32/0.64    k2_xboole_0(sK1,sK3) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl5_46),
% 2.32/0.64    inference(superposition,[],[f41,f585])).
% 2.32/0.64  fof(f585,plain,(
% 2.32/0.64    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(sK1,sK3) | ~spl5_46),
% 2.32/0.64    inference(avatar_component_clause,[],[f583])).
% 2.32/0.64  fof(f625,plain,(
% 2.32/0.64    spl5_47 | ~spl5_45),
% 2.32/0.64    inference(avatar_split_clause,[],[f612,f547,f614])).
% 2.32/0.64  fof(f547,plain,(
% 2.32/0.64    spl5_45 <=> k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK1,sK2)),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 2.32/0.64  fof(f612,plain,(
% 2.32/0.64    k2_xboole_0(sK1,sK2) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl5_45),
% 2.32/0.64    inference(superposition,[],[f41,f549])).
% 2.32/0.64  fof(f549,plain,(
% 2.32/0.64    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK1,sK2) | ~spl5_45),
% 2.32/0.64    inference(avatar_component_clause,[],[f547])).
% 2.32/0.64  fof(f586,plain,(
% 2.32/0.64    spl5_46 | ~spl5_44),
% 2.32/0.64    inference(avatar_split_clause,[],[f581,f519,f583])).
% 2.32/0.64  fof(f519,plain,(
% 2.32/0.64    spl5_44 <=> sK3 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 2.32/0.64  fof(f581,plain,(
% 2.32/0.64    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(sK1,sK3) | ~spl5_44),
% 2.32/0.64    inference(forward_demodulation,[],[f580,f41])).
% 2.32/0.64  fof(f580,plain,(
% 2.32/0.64    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(sK3,sK1) | ~spl5_44),
% 2.32/0.64    inference(forward_demodulation,[],[f579,f43])).
% 2.32/0.64  fof(f579,plain,(
% 2.32/0.64    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(sK3,k4_xboole_0(sK1,sK3)) | ~spl5_44),
% 2.32/0.64    inference(forward_demodulation,[],[f577,f41])).
% 2.32/0.64  fof(f577,plain,(
% 2.32/0.64    k2_xboole_0(k4_xboole_0(sK1,sK3),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK3),sK3) | ~spl5_44),
% 2.32/0.64    inference(superposition,[],[f43,f521])).
% 2.32/0.64  fof(f521,plain,(
% 2.32/0.64    sK3 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~spl5_44),
% 2.32/0.64    inference(avatar_component_clause,[],[f519])).
% 2.32/0.64  fof(f550,plain,(
% 2.32/0.64    spl5_45 | ~spl5_42),
% 2.32/0.64    inference(avatar_split_clause,[],[f545,f489,f547])).
% 2.32/0.64  fof(f489,plain,(
% 2.32/0.64    spl5_42 <=> sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 2.32/0.64  fof(f545,plain,(
% 2.32/0.64    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK1,sK2) | ~spl5_42),
% 2.32/0.64    inference(forward_demodulation,[],[f544,f41])).
% 2.32/0.64  fof(f544,plain,(
% 2.32/0.64    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK2,sK1) | ~spl5_42),
% 2.32/0.64    inference(forward_demodulation,[],[f543,f43])).
% 2.32/0.64  fof(f543,plain,(
% 2.32/0.64    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) | ~spl5_42),
% 2.32/0.64    inference(forward_demodulation,[],[f541,f41])).
% 2.32/0.64  fof(f541,plain,(
% 2.32/0.64    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2) | ~spl5_42),
% 2.32/0.64    inference(superposition,[],[f43,f491])).
% 2.32/0.64  fof(f491,plain,(
% 2.32/0.64    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~spl5_42),
% 2.32/0.64    inference(avatar_component_clause,[],[f489])).
% 2.32/0.64  fof(f532,plain,(
% 2.32/0.64    spl5_43),
% 2.32/0.64    inference(avatar_contradiction_clause,[],[f531])).
% 2.32/0.64  fof(f531,plain,(
% 2.32/0.64    $false | spl5_43),
% 2.32/0.64    inference(subsumption_resolution,[],[f530,f38])).
% 2.32/0.64  fof(f38,plain,(
% 2.32/0.64    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 2.32/0.64    inference(cnf_transformation,[],[f11])).
% 2.32/0.64  fof(f11,axiom,(
% 2.32/0.64    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 2.32/0.64  fof(f530,plain,(
% 2.32/0.64    v1_xboole_0(k1_zfmisc_1(sK1)) | spl5_43),
% 2.32/0.64    inference(subsumption_resolution,[],[f525,f180])).
% 2.32/0.64  fof(f180,plain,(
% 2.32/0.64    ( ! [X0,X1] : (r2_hidden(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 2.32/0.64    inference(unit_resulting_resolution,[],[f40,f59,f51])).
% 2.32/0.64  fof(f51,plain,(
% 2.32/0.64    ( ! [X0,X3,X1] : (~sP0(X0,X1) | ~r1_tarski(X3,X0) | r2_hidden(X3,X1)) )),
% 2.32/0.64    inference(cnf_transformation,[],[f33])).
% 2.32/0.64  fof(f33,plain,(
% 2.32/0.64    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 2.32/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f31,f32])).
% 2.32/0.64  fof(f32,plain,(
% 2.32/0.64    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK4(X0,X1),X0) | ~r2_hidden(sK4(X0,X1),X1)) & (r1_tarski(sK4(X0,X1),X0) | r2_hidden(sK4(X0,X1),X1))))),
% 2.32/0.64    introduced(choice_axiom,[])).
% 2.32/0.64  fof(f31,plain,(
% 2.32/0.64    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | ~sP0(X0,X1)))),
% 2.32/0.64    inference(rectify,[],[f30])).
% 2.32/0.64  fof(f30,plain,(
% 2.32/0.64    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 2.32/0.64    inference(nnf_transformation,[],[f24])).
% 2.32/0.64  fof(f24,plain,(
% 2.32/0.64    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.32/0.64    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.32/0.64  fof(f59,plain,(
% 2.32/0.64    ( ! [X0] : (sP0(X0,k1_zfmisc_1(X0))) )),
% 2.32/0.64    inference(equality_resolution,[],[f54])).
% 2.32/0.64  fof(f54,plain,(
% 2.32/0.64    ( ! [X0,X1] : (sP0(X0,X1) | k1_zfmisc_1(X0) != X1) )),
% 2.32/0.64    inference(cnf_transformation,[],[f34])).
% 2.32/0.64  fof(f34,plain,(
% 2.32/0.64    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k1_zfmisc_1(X0) != X1))),
% 2.32/0.64    inference(nnf_transformation,[],[f25])).
% 2.32/0.64  fof(f25,plain,(
% 2.32/0.64    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> sP0(X0,X1))),
% 2.32/0.64    inference(definition_folding,[],[f8,f24])).
% 2.32/0.64  fof(f8,axiom,(
% 2.32/0.64    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 2.32/0.64  fof(f525,plain,(
% 2.32/0.64    ~r2_hidden(k4_xboole_0(sK1,sK3),k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) | spl5_43),
% 2.32/0.64    inference(resolution,[],[f517,f45])).
% 2.32/0.64  fof(f45,plain,(
% 2.32/0.64    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.32/0.64    inference(cnf_transformation,[],[f29])).
% 2.32/0.64  fof(f29,plain,(
% 2.32/0.64    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 2.32/0.64    inference(nnf_transformation,[],[f18])).
% 2.32/0.64  fof(f18,plain,(
% 2.32/0.64    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.32/0.64    inference(ennf_transformation,[],[f9])).
% 2.32/0.64  fof(f9,axiom,(
% 2.32/0.64    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.32/0.64  fof(f517,plain,(
% 2.32/0.64    ~m1_subset_1(k4_xboole_0(sK1,sK3),k1_zfmisc_1(sK1)) | spl5_43),
% 2.32/0.64    inference(avatar_component_clause,[],[f515])).
% 2.32/0.64  fof(f515,plain,(
% 2.32/0.64    spl5_43 <=> m1_subset_1(k4_xboole_0(sK1,sK3),k1_zfmisc_1(sK1))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 2.32/0.64  fof(f523,plain,(
% 2.32/0.64    ~spl5_43 | spl5_44 | ~spl5_40),
% 2.32/0.64    inference(avatar_split_clause,[],[f513,f477,f519,f515])).
% 2.32/0.64  fof(f477,plain,(
% 2.32/0.64    spl5_40 <=> sK3 = k3_subset_1(sK1,k4_xboole_0(sK1,sK3))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 2.32/0.64  fof(f513,plain,(
% 2.32/0.64    sK3 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) | ~m1_subset_1(k4_xboole_0(sK1,sK3),k1_zfmisc_1(sK1)) | ~spl5_40),
% 2.32/0.64    inference(superposition,[],[f48,f479])).
% 2.32/0.64  fof(f479,plain,(
% 2.32/0.64    sK3 = k3_subset_1(sK1,k4_xboole_0(sK1,sK3)) | ~spl5_40),
% 2.32/0.64    inference(avatar_component_clause,[],[f477])).
% 2.32/0.64  fof(f48,plain,(
% 2.32/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.32/0.64    inference(cnf_transformation,[],[f19])).
% 2.32/0.64  fof(f19,plain,(
% 2.32/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.32/0.64    inference(ennf_transformation,[],[f10])).
% 2.32/0.64  fof(f10,axiom,(
% 2.32/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.32/0.64  fof(f502,plain,(
% 2.32/0.64    spl5_41),
% 2.32/0.64    inference(avatar_contradiction_clause,[],[f501])).
% 2.32/0.64  fof(f501,plain,(
% 2.32/0.64    $false | spl5_41),
% 2.32/0.64    inference(subsumption_resolution,[],[f500,f38])).
% 2.32/0.64  fof(f500,plain,(
% 2.32/0.64    v1_xboole_0(k1_zfmisc_1(sK1)) | spl5_41),
% 2.32/0.64    inference(subsumption_resolution,[],[f495,f180])).
% 2.32/0.64  fof(f495,plain,(
% 2.32/0.64    ~r2_hidden(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) | spl5_41),
% 2.32/0.64    inference(resolution,[],[f487,f45])).
% 2.32/0.64  fof(f487,plain,(
% 2.32/0.64    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) | spl5_41),
% 2.32/0.64    inference(avatar_component_clause,[],[f485])).
% 2.32/0.64  fof(f485,plain,(
% 2.32/0.64    spl5_41 <=> m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 2.32/0.64  fof(f493,plain,(
% 2.32/0.64    ~spl5_41 | spl5_42 | ~spl5_39),
% 2.32/0.64    inference(avatar_split_clause,[],[f483,f471,f489,f485])).
% 2.32/0.64  fof(f471,plain,(
% 2.32/0.64    spl5_39 <=> sK2 = k3_subset_1(sK1,k4_xboole_0(sK1,sK2))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 2.32/0.64  fof(f483,plain,(
% 2.32/0.64    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(sK1)) | ~spl5_39),
% 2.32/0.64    inference(superposition,[],[f48,f473])).
% 2.32/0.64  fof(f473,plain,(
% 2.32/0.64    sK2 = k3_subset_1(sK1,k4_xboole_0(sK1,sK2)) | ~spl5_39),
% 2.32/0.64    inference(avatar_component_clause,[],[f471])).
% 2.32/0.64  fof(f480,plain,(
% 2.32/0.64    spl5_40 | ~spl5_2 | ~spl5_13),
% 2.32/0.64    inference(avatar_split_clause,[],[f475,f295,f66,f477])).
% 2.32/0.64  fof(f295,plain,(
% 2.32/0.64    spl5_13 <=> k4_xboole_0(sK1,sK3) = k3_subset_1(sK1,sK3)),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.32/0.64  fof(f475,plain,(
% 2.32/0.64    sK3 = k3_subset_1(sK1,k4_xboole_0(sK1,sK3)) | (~spl5_2 | ~spl5_13)),
% 2.32/0.64    inference(forward_demodulation,[],[f457,f297])).
% 2.32/0.64  fof(f297,plain,(
% 2.32/0.64    k4_xboole_0(sK1,sK3) = k3_subset_1(sK1,sK3) | ~spl5_13),
% 2.32/0.64    inference(avatar_component_clause,[],[f295])).
% 2.32/0.64  fof(f457,plain,(
% 2.32/0.64    sK3 = k3_subset_1(sK1,k3_subset_1(sK1,sK3)) | ~spl5_2),
% 2.32/0.64    inference(unit_resulting_resolution,[],[f68,f49])).
% 2.32/0.64  fof(f49,plain,(
% 2.32/0.64    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.32/0.64    inference(cnf_transformation,[],[f20])).
% 2.32/0.64  fof(f20,plain,(
% 2.32/0.64    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.32/0.64    inference(ennf_transformation,[],[f12])).
% 2.32/0.64  fof(f12,axiom,(
% 2.32/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.32/0.64  fof(f474,plain,(
% 2.32/0.64    spl5_39 | ~spl5_3 | ~spl5_12),
% 2.32/0.64    inference(avatar_split_clause,[],[f469,f290,f71,f471])).
% 2.32/0.64  fof(f290,plain,(
% 2.32/0.64    spl5_12 <=> k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2)),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.32/0.64  fof(f469,plain,(
% 2.32/0.64    sK2 = k3_subset_1(sK1,k4_xboole_0(sK1,sK2)) | (~spl5_3 | ~spl5_12)),
% 2.32/0.64    inference(forward_demodulation,[],[f458,f292])).
% 2.32/0.64  fof(f292,plain,(
% 2.32/0.64    k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) | ~spl5_12),
% 2.32/0.64    inference(avatar_component_clause,[],[f290])).
% 2.32/0.64  fof(f458,plain,(
% 2.32/0.64    sK2 = k3_subset_1(sK1,k3_subset_1(sK1,sK2)) | ~spl5_3),
% 2.32/0.64    inference(unit_resulting_resolution,[],[f73,f49])).
% 2.32/0.64  fof(f447,plain,(
% 2.32/0.64    ~spl5_37 | spl5_35),
% 2.32/0.64    inference(avatar_split_clause,[],[f433,f427,f444])).
% 2.32/0.64  fof(f427,plain,(
% 2.32/0.64    spl5_35 <=> r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 2.32/0.64  fof(f433,plain,(
% 2.32/0.64    ~r1_tarski(k4_subset_1(sK1,sK2,sK3),sK1) | spl5_35),
% 2.32/0.64    inference(unit_resulting_resolution,[],[f59,f429,f51])).
% 2.32/0.64  fof(f429,plain,(
% 2.32/0.64    ~r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | spl5_35),
% 2.32/0.64    inference(avatar_component_clause,[],[f427])).
% 2.32/0.64  fof(f432,plain,(
% 2.32/0.64    ~spl5_35 | spl5_14),
% 2.32/0.64    inference(avatar_split_clause,[],[f431,f300,f427])).
% 2.32/0.64  fof(f300,plain,(
% 2.32/0.64    spl5_14 <=> m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.32/0.64  fof(f431,plain,(
% 2.32/0.64    ~r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | spl5_14),
% 2.32/0.64    inference(subsumption_resolution,[],[f423,f38])).
% 2.32/0.64  fof(f423,plain,(
% 2.32/0.64    ~r2_hidden(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | v1_xboole_0(k1_zfmisc_1(sK1)) | spl5_14),
% 2.32/0.64    inference(resolution,[],[f302,f45])).
% 2.32/0.64  fof(f302,plain,(
% 2.32/0.64    ~m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | spl5_14),
% 2.32/0.64    inference(avatar_component_clause,[],[f300])).
% 2.32/0.64  fof(f401,plain,(
% 2.32/0.64    ~spl5_30 | ~spl5_12 | spl5_15),
% 2.32/0.64    inference(avatar_split_clause,[],[f392,f304,f290,f398])).
% 2.32/0.64  fof(f304,plain,(
% 2.32/0.64    spl5_15 <=> r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.32/0.64  fof(f392,plain,(
% 2.32/0.64    ~r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k4_xboole_0(sK1,sK2)) | (~spl5_12 | spl5_15)),
% 2.32/0.64    inference(backward_demodulation,[],[f306,f292])).
% 2.32/0.64  fof(f306,plain,(
% 2.32/0.64    ~r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) | spl5_15),
% 2.32/0.64    inference(avatar_component_clause,[],[f304])).
% 2.32/0.64  fof(f307,plain,(
% 2.32/0.64    ~spl5_14 | ~spl5_15 | spl5_1),
% 2.32/0.64    inference(avatar_split_clause,[],[f270,f61,f304,f300])).
% 2.32/0.64  fof(f61,plain,(
% 2.32/0.64    spl5_1 <=> r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 2.32/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.32/0.64  fof(f270,plain,(
% 2.32/0.64    ~r1_tarski(k4_xboole_0(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) | ~m1_subset_1(k4_subset_1(sK1,sK2,sK3),k1_zfmisc_1(sK1)) | spl5_1),
% 2.32/0.64    inference(superposition,[],[f63,f48])).
% 2.32/0.64  fof(f63,plain,(
% 2.32/0.64    ~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) | spl5_1),
% 2.32/0.64    inference(avatar_component_clause,[],[f61])).
% 2.32/0.64  fof(f298,plain,(
% 2.32/0.64    spl5_13 | ~spl5_2),
% 2.32/0.64    inference(avatar_split_clause,[],[f266,f66,f295])).
% 2.32/0.64  fof(f266,plain,(
% 2.32/0.64    k4_xboole_0(sK1,sK3) = k3_subset_1(sK1,sK3) | ~spl5_2),
% 2.32/0.64    inference(unit_resulting_resolution,[],[f68,f48])).
% 2.32/0.64  fof(f293,plain,(
% 2.32/0.64    spl5_12 | ~spl5_3),
% 2.32/0.64    inference(avatar_split_clause,[],[f267,f71,f290])).
% 2.32/0.64  fof(f267,plain,(
% 2.32/0.64    k3_subset_1(sK1,sK2) = k4_xboole_0(sK1,sK2) | ~spl5_3),
% 2.32/0.64    inference(unit_resulting_resolution,[],[f73,f48])).
% 2.32/0.64  fof(f74,plain,(
% 2.32/0.64    spl5_3),
% 2.32/0.64    inference(avatar_split_clause,[],[f35,f71])).
% 2.32/0.64  fof(f35,plain,(
% 2.32/0.64    m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.32/0.64    inference(cnf_transformation,[],[f28])).
% 2.32/0.64  fof(f28,plain,(
% 2.32/0.64    (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1))),
% 2.32/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f17,f27,f26])).
% 2.32/0.64  fof(f26,plain,(
% 2.32/0.64    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) & m1_subset_1(sK2,k1_zfmisc_1(sK1)))),
% 2.32/0.64    introduced(choice_axiom,[])).
% 2.32/0.64  fof(f27,plain,(
% 2.32/0.64    ? [X2] : (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,X2)),k3_subset_1(sK1,sK2)) & m1_subset_1(X2,k1_zfmisc_1(sK1))) => (~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2)) & m1_subset_1(sK3,k1_zfmisc_1(sK1)))),
% 2.32/0.64    introduced(choice_axiom,[])).
% 2.32/0.64  fof(f17,plain,(
% 2.32/0.64    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.32/0.64    inference(ennf_transformation,[],[f15])).
% 2.32/0.64  fof(f15,negated_conjecture,(
% 2.32/0.64    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.32/0.64    inference(negated_conjecture,[],[f14])).
% 2.32/0.64  fof(f14,conjecture,(
% 2.32/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.32/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 2.32/0.64  fof(f69,plain,(
% 2.32/0.64    spl5_2),
% 2.32/0.64    inference(avatar_split_clause,[],[f36,f66])).
% 2.32/0.64  fof(f36,plain,(
% 2.32/0.64    m1_subset_1(sK3,k1_zfmisc_1(sK1))),
% 2.32/0.64    inference(cnf_transformation,[],[f28])).
% 2.32/0.64  fof(f64,plain,(
% 2.32/0.64    ~spl5_1),
% 2.32/0.64    inference(avatar_split_clause,[],[f37,f61])).
% 2.32/0.64  fof(f37,plain,(
% 2.32/0.64    ~r1_tarski(k3_subset_1(sK1,k4_subset_1(sK1,sK2,sK3)),k3_subset_1(sK1,sK2))),
% 2.32/0.64    inference(cnf_transformation,[],[f28])).
% 2.32/0.64  % SZS output end Proof for theBenchmark
% 2.32/0.64  % (21444)------------------------------
% 2.32/0.64  % (21444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.64  % (21444)Termination reason: Refutation
% 2.32/0.64  
% 2.32/0.64  % (21444)Memory used [KB]: 13688
% 2.32/0.64  % (21444)Time elapsed: 0.232 s
% 2.32/0.64  % (21444)------------------------------
% 2.32/0.64  % (21444)------------------------------
% 2.32/0.64  % (21427)Success in time 0.285 s
%------------------------------------------------------------------------------
