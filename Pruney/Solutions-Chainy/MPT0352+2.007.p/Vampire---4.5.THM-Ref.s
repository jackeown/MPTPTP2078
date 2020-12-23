%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:14 EST 2020

% Result     : Theorem 6.30s
% Output     : Refutation 6.30s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 340 expanded)
%              Number of leaves         :   30 ( 116 expanded)
%              Depth                    :   12
%              Number of atoms          :  310 ( 728 expanded)
%              Number of equality atoms :   37 ( 110 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f76,f94,f99,f103,f351,f358,f2266,f2401,f3115,f3168,f3186,f6156,f6157,f6265,f6315,f6356,f6441])).

fof(f6441,plain,
    ( ~ spl4_100
    | spl4_1
    | ~ spl4_61 ),
    inference(avatar_split_clause,[],[f6435,f1413,f68,f2376])).

fof(f2376,plain,
    ( spl4_100
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).

fof(f68,plain,
    ( spl4_1
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1413,plain,
    ( spl4_61
  <=> sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).

fof(f6435,plain,
    ( r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl4_61 ),
    inference(superposition,[],[f6405,f453])).

fof(f453,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4
      | ~ r1_tarski(X4,X5) ) ),
    inference(superposition,[],[f61,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f61,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f38,f38])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f6405,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2)
    | ~ spl4_61 ),
    inference(superposition,[],[f2790,f1415])).

fof(f1415,plain,
    ( sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ spl4_61 ),
    inference(avatar_component_clause,[],[f1413])).

fof(f2790,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0) ),
    inference(resolution,[],[f387,f115])).

fof(f115,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f56,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f387,plain,(
    ! [X35,X36,X34] :
      ( ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(X34,X35),X36),X35)
      | r1_tarski(k4_xboole_0(k2_xboole_0(X34,X35),X36),X34) ) ),
    inference(resolution,[],[f59,f35])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f6356,plain,
    ( ~ spl4_15
    | spl4_61
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f6317,f1216,f1413,f334])).

fof(f334,plain,
    ( spl4_15
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1216,plain,
    ( spl4_49
  <=> sK0 = k2_xboole_0(sK2,k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f6317,plain,
    ( sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_49 ),
    inference(superposition,[],[f1218,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f1218,plain,
    ( sK0 = k2_xboole_0(sK2,k3_subset_1(sK0,sK1))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f1216])).

fof(f6315,plain,
    ( spl4_49
    | ~ spl4_50
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f6311,f329,f1220,f1216])).

fof(f1220,plain,
    ( spl4_50
  <=> r1_tarski(k2_xboole_0(sK2,k3_subset_1(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f329,plain,
    ( spl4_14
  <=> r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f6311,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,k3_subset_1(sK0,sK1)),sK0)
    | sK0 = k2_xboole_0(sK2,k3_subset_1(sK0,sK1))
    | ~ spl4_14 ),
    inference(resolution,[],[f6274,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f6274,plain,
    ( r1_tarski(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK1)))
    | ~ spl4_14 ),
    inference(resolution,[],[f331,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f331,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f329])).

fof(f6265,plain,
    ( ~ spl4_12
    | spl4_14
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f6263,f72,f329,f320])).

fof(f320,plain,
    ( spl4_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f72,plain,
    ( spl4_2
  <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f6263,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(superposition,[],[f73,f47])).

fof(f73,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f6157,plain,
    ( ~ spl4_4
    | spl4_60 ),
    inference(avatar_contradiction_clause,[],[f6137])).

fof(f6137,plain,
    ( $false
    | ~ spl4_4
    | spl4_60 ),
    inference(subsumption_resolution,[],[f1403,f5502])).

fof(f5502,plain,
    ( ! [X121] : r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,X121)),sK0)
    | ~ spl4_4 ),
    inference(superposition,[],[f3222,f4936])).

fof(f4936,plain,(
    ! [X2,X1] : k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1 ),
    inference(resolution,[],[f221,f113])).

fof(f113,plain,(
    ! [X4,X2,X3] : r1_tarski(k4_xboole_0(k4_xboole_0(X2,X3),X4),X2) ),
    inference(resolution,[],[f55,f35])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f221,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(k4_xboole_0(X9,X8),X8)
      | k2_xboole_0(X8,X9) = X8 ) ),
    inference(superposition,[],[f106,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f106,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f46,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f3222,plain,
    ( ! [X2] : r1_tarski(k2_xboole_0(sK2,X2),k2_xboole_0(sK0,X2))
    | ~ spl4_4 ),
    inference(superposition,[],[f2957,f37])).

fof(f2957,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(X0,sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f2816,f58])).

fof(f2816,plain,
    ( ! [X27] : r1_tarski(k4_xboole_0(k2_xboole_0(sK2,X27),X27),sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f2790,f546])).

fof(f546,plain,
    ( ! [X60] :
        ( ~ r1_tarski(X60,sK2)
        | r1_tarski(X60,sK0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f119,f104])).

fof(f104,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f93,f65])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f93,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_4
  <=> r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f57,f46])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f1403,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK0)
    | spl4_60 ),
    inference(avatar_component_clause,[],[f1401])).

fof(f1401,plain,
    ( spl4_60
  <=> r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).

fof(f6156,plain,
    ( ~ spl4_1
    | ~ spl4_4
    | spl4_61 ),
    inference(avatar_contradiction_clause,[],[f6139])).

fof(f6139,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4
    | spl4_61 ),
    inference(unit_resulting_resolution,[],[f1414,f2592,f5502,f50])).

fof(f2592,plain,
    ( ! [X0] : r1_tarski(X0,k2_xboole_0(sK2,k4_xboole_0(X0,sK1)))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f2581,f37])).

fof(f2581,plain,
    ( ! [X0] : r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,sK1),sK2))
    | ~ spl4_1 ),
    inference(resolution,[],[f2443,f58])).

fof(f2443,plain,
    ( ! [X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,sK1)),sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f2258,f457])).

fof(f457,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4) ),
    inference(superposition,[],[f35,f61])).

fof(f2258,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_tarski(X0,sK2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f69,f119])).

fof(f69,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f1414,plain,
    ( sK0 != k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | spl4_61 ),
    inference(avatar_component_clause,[],[f1413])).

fof(f3186,plain,
    ( ~ spl4_15
    | ~ spl4_60
    | spl4_50 ),
    inference(avatar_split_clause,[],[f3183,f1220,f1401,f334])).

fof(f3183,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_50 ),
    inference(superposition,[],[f1222,f47])).

fof(f1222,plain,
    ( ~ r1_tarski(k2_xboole_0(sK2,k3_subset_1(sK0,sK1)),sK0)
    | spl4_50 ),
    inference(avatar_component_clause,[],[f1220])).

fof(f3168,plain,
    ( ~ spl4_15
    | ~ spl4_61
    | spl4_49 ),
    inference(avatar_split_clause,[],[f3165,f1216,f1413,f334])).

fof(f3165,plain,
    ( sK0 != k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_49 ),
    inference(superposition,[],[f1217,f47])).

fof(f1217,plain,
    ( sK0 != k2_xboole_0(sK2,k3_subset_1(sK0,sK1))
    | spl4_49 ),
    inference(avatar_component_clause,[],[f1216])).

fof(f3115,plain,
    ( spl4_14
    | ~ spl4_49 ),
    inference(avatar_contradiction_clause,[],[f3109])).

fof(f3109,plain,
    ( $false
    | spl4_14
    | ~ spl4_49 ),
    inference(subsumption_resolution,[],[f330,f2882])).

fof(f2882,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ spl4_49 ),
    inference(superposition,[],[f2819,f1218])).

fof(f2819,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(k2_xboole_0(X5,X4),X5),X4) ),
    inference(superposition,[],[f2790,f37])).

fof(f330,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f329])).

fof(f2401,plain,
    ( ~ spl4_5
    | spl4_100 ),
    inference(avatar_contradiction_clause,[],[f2390])).

fof(f2390,plain,
    ( $false
    | ~ spl4_5
    | spl4_100 ),
    inference(subsumption_resolution,[],[f110,f2378])).

fof(f2378,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_100 ),
    inference(avatar_component_clause,[],[f2376])).

fof(f110,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f98,f65])).

fof(f98,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_5
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f2266,plain,
    ( ~ spl4_12
    | ~ spl4_14
    | spl4_2 ),
    inference(avatar_split_clause,[],[f2264,f72,f329,f320])).

fof(f2264,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl4_2 ),
    inference(superposition,[],[f74,f47])).

fof(f74,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f358,plain,(
    spl4_15 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | spl4_15 ),
    inference(subsumption_resolution,[],[f33,f336])).

fof(f336,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f334])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_tarski(X1,X2)
          <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => ( r1_tarski(X1,X2)
            <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f351,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | spl4_12 ),
    inference(subsumption_resolution,[],[f32,f322])).

fof(f322,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f320])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f34,f89])).

fof(f89,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f99,plain,
    ( spl4_3
    | spl4_5 ),
    inference(avatar_split_clause,[],[f84,f96,f87])).

fof(f84,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f44,f33])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f94,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f83,f91,f87])).

fof(f83,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f44,f32])).

fof(f76,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f30,f72,f68])).

fof(f30,plain,
    ( r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f75,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f31,f72,f68])).

fof(f31,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:31:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.48  % (2015)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (2022)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (2027)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.53  % (2020)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (2027)Refutation not found, incomplete strategy% (2027)------------------------------
% 0.20/0.53  % (2027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2027)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2027)Memory used [KB]: 10618
% 0.20/0.53  % (2027)Time elapsed: 0.084 s
% 0.20/0.53  % (2027)------------------------------
% 0.20/0.53  % (2027)------------------------------
% 0.20/0.53  % (2020)Refutation not found, incomplete strategy% (2020)------------------------------
% 0.20/0.53  % (2020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2020)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2020)Memory used [KB]: 10746
% 0.20/0.53  % (2020)Time elapsed: 0.114 s
% 0.20/0.53  % (2020)------------------------------
% 0.20/0.53  % (2020)------------------------------
% 0.20/0.53  % (2013)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (2029)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (2036)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.54  % (2018)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.55  % (2034)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.34/0.55  % (2017)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.55  % (2009)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.55  % (2041)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.55  % (2033)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.55  % (2023)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.34/0.56  % (2035)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.56  % (2023)Refutation not found, incomplete strategy% (2023)------------------------------
% 1.34/0.56  % (2023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (2023)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.56  
% 1.34/0.56  % (2023)Memory used [KB]: 10618
% 1.34/0.56  % (2023)Time elapsed: 0.144 s
% 1.34/0.56  % (2023)------------------------------
% 1.34/0.56  % (2023)------------------------------
% 1.51/0.56  % (2026)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.51/0.56  % (2039)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.51/0.57  % (2016)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.51/0.57  % (2010)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.51/0.57  % (2010)Refutation not found, incomplete strategy% (2010)------------------------------
% 1.51/0.57  % (2010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (2010)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (2010)Memory used [KB]: 1663
% 1.51/0.57  % (2010)Time elapsed: 0.148 s
% 1.51/0.57  % (2010)------------------------------
% 1.51/0.57  % (2010)------------------------------
% 1.51/0.57  % (2014)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.51/0.57  % (2025)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.51/0.57  % (2030)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.51/0.58  % (2031)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.51/0.58  % (2024)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.51/0.58  % (2028)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.51/0.58  % (2012)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.51/0.58  % (2040)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.51/0.58  % (2040)Refutation not found, incomplete strategy% (2040)------------------------------
% 1.51/0.58  % (2040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (2040)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (2040)Memory used [KB]: 10746
% 1.51/0.58  % (2040)Time elapsed: 0.170 s
% 1.51/0.58  % (2040)------------------------------
% 1.51/0.58  % (2040)------------------------------
% 1.51/0.58  % (2019)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.51/0.59  % (2032)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.51/0.59  % (2038)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.51/0.62  % (2038)Refutation not found, incomplete strategy% (2038)------------------------------
% 1.51/0.62  % (2038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.62  % (2038)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.62  
% 1.51/0.62  % (2038)Memory used [KB]: 6524
% 1.51/0.62  % (2038)Time elapsed: 0.193 s
% 1.51/0.62  % (2038)------------------------------
% 1.51/0.62  % (2038)------------------------------
% 1.97/0.64  % (2060)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.97/0.66  % (2061)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.22/0.69  % (2064)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.22/0.69  % (2064)Refutation not found, incomplete strategy% (2064)------------------------------
% 2.22/0.69  % (2064)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.69  % (2064)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.69  
% 2.22/0.69  % (2064)Memory used [KB]: 6140
% 2.22/0.69  % (2064)Time elapsed: 0.094 s
% 2.22/0.69  % (2064)------------------------------
% 2.22/0.69  % (2064)------------------------------
% 2.22/0.70  % (2013)Refutation not found, incomplete strategy% (2013)------------------------------
% 2.22/0.70  % (2013)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.70  % (2013)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.70  
% 2.22/0.70  % (2013)Memory used [KB]: 6140
% 2.22/0.70  % (2013)Time elapsed: 0.268 s
% 2.22/0.70  % (2013)------------------------------
% 2.22/0.70  % (2013)------------------------------
% 2.22/0.71  % (2065)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.22/0.71  % (2009)Refutation not found, incomplete strategy% (2009)------------------------------
% 2.22/0.71  % (2009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.72  % (2066)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.22/0.73  % (2026)Refutation not found, incomplete strategy% (2026)------------------------------
% 2.22/0.73  % (2026)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.22/0.73  % (2026)Termination reason: Refutation not found, incomplete strategy
% 2.22/0.73  
% 2.22/0.73  % (2026)Memory used [KB]: 6268
% 2.22/0.73  % (2026)Time elapsed: 0.298 s
% 2.22/0.73  % (2026)------------------------------
% 2.22/0.73  % (2026)------------------------------
% 2.67/0.73  % (2009)Termination reason: Refutation not found, incomplete strategy
% 2.67/0.73  
% 2.67/0.73  % (2009)Memory used [KB]: 1791
% 2.67/0.73  % (2009)Time elapsed: 0.303 s
% 2.67/0.73  % (2009)------------------------------
% 2.67/0.73  % (2009)------------------------------
% 2.87/0.77  % (2067)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.87/0.79  % (2069)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 3.20/0.83  % (2070)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 3.20/0.83  % (2035)Time limit reached!
% 3.20/0.83  % (2035)------------------------------
% 3.20/0.83  % (2035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.83  % (2035)Termination reason: Time limit
% 3.20/0.83  
% 3.20/0.83  % (2035)Memory used [KB]: 12409
% 3.20/0.83  % (2035)Time elapsed: 0.412 s
% 3.20/0.83  % (2035)------------------------------
% 3.20/0.83  % (2035)------------------------------
% 3.42/0.86  % (2071)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 3.42/0.87  % (2072)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 3.42/0.90  % (2012)Time limit reached!
% 3.42/0.90  % (2012)------------------------------
% 3.42/0.90  % (2012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.90  % (2012)Termination reason: Time limit
% 3.42/0.90  
% 3.42/0.90  % (2012)Memory used [KB]: 6652
% 3.42/0.90  % (2012)Time elapsed: 0.404 s
% 3.42/0.90  % (2012)------------------------------
% 3.42/0.90  % (2012)------------------------------
% 3.42/0.92  % (2025)Time limit reached!
% 3.42/0.92  % (2025)------------------------------
% 3.42/0.92  % (2025)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.92  % (2025)Termination reason: Time limit
% 3.42/0.92  
% 3.42/0.92  % (2025)Memory used [KB]: 3326
% 3.42/0.92  % (2025)Time elapsed: 0.504 s
% 3.42/0.92  % (2025)------------------------------
% 3.42/0.92  % (2025)------------------------------
% 3.42/0.92  % (2016)Time limit reached!
% 3.42/0.92  % (2016)------------------------------
% 3.42/0.92  % (2016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.42/0.92  % (2016)Termination reason: Time limit
% 3.42/0.92  
% 3.42/0.92  % (2016)Memory used [KB]: 13816
% 3.42/0.92  % (2016)Time elapsed: 0.512 s
% 3.42/0.92  % (2016)------------------------------
% 3.42/0.92  % (2016)------------------------------
% 3.78/0.93  % (2041)Time limit reached!
% 3.78/0.93  % (2041)------------------------------
% 3.78/0.93  % (2041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.78/0.93  % (2041)Termination reason: Time limit
% 3.78/0.93  
% 3.78/0.93  % (2041)Memory used [KB]: 6140
% 3.78/0.93  % (2041)Time elapsed: 0.520 s
% 3.78/0.93  % (2041)------------------------------
% 3.78/0.93  % (2041)------------------------------
% 3.78/0.96  % (2073)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 3.94/1.03  % (2074)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 3.94/1.03  % (2017)Time limit reached!
% 3.94/1.03  % (2017)------------------------------
% 3.94/1.03  % (2017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.94/1.03  % (2017)Termination reason: Time limit
% 3.94/1.03  
% 3.94/1.03  % (2017)Memory used [KB]: 6268
% 3.94/1.03  % (2017)Time elapsed: 0.618 s
% 3.94/1.03  % (2017)------------------------------
% 3.94/1.03  % (2017)------------------------------
% 4.24/1.04  % (2075)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 4.24/1.05  % (2076)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 4.24/1.07  % (2077)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 6.03/1.17  % (2116)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 6.30/1.19  % (2024)Refutation found. Thanks to Tanya!
% 6.30/1.19  % SZS status Theorem for theBenchmark
% 6.30/1.21  % SZS output start Proof for theBenchmark
% 6.30/1.21  fof(f6445,plain,(
% 6.30/1.21    $false),
% 6.30/1.21    inference(avatar_sat_refutation,[],[f75,f76,f94,f99,f103,f351,f358,f2266,f2401,f3115,f3168,f3186,f6156,f6157,f6265,f6315,f6356,f6441])).
% 6.30/1.21  fof(f6441,plain,(
% 6.30/1.21    ~spl4_100 | spl4_1 | ~spl4_61),
% 6.30/1.21    inference(avatar_split_clause,[],[f6435,f1413,f68,f2376])).
% 6.30/1.21  fof(f2376,plain,(
% 6.30/1.21    spl4_100 <=> r1_tarski(sK1,sK0)),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_100])])).
% 6.30/1.21  fof(f68,plain,(
% 6.30/1.21    spl4_1 <=> r1_tarski(sK1,sK2)),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 6.30/1.21  fof(f1413,plain,(
% 6.30/1.21    spl4_61 <=> sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1))),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_61])])).
% 6.30/1.21  fof(f6435,plain,(
% 6.30/1.21    r1_tarski(sK1,sK2) | ~r1_tarski(sK1,sK0) | ~spl4_61),
% 6.30/1.21    inference(superposition,[],[f6405,f453])).
% 6.30/1.21  fof(f453,plain,(
% 6.30/1.21    ( ! [X4,X5] : (k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4 | ~r1_tarski(X4,X5)) )),
% 6.30/1.21    inference(superposition,[],[f61,f62])).
% 6.30/1.21  fof(f62,plain,(
% 6.30/1.21    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 6.30/1.21    inference(definition_unfolding,[],[f45,f38])).
% 6.30/1.21  fof(f38,plain,(
% 6.30/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.30/1.21    inference(cnf_transformation,[],[f12])).
% 6.30/1.21  fof(f12,axiom,(
% 6.30/1.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.30/1.21  fof(f45,plain,(
% 6.30/1.21    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 6.30/1.21    inference(cnf_transformation,[],[f22])).
% 6.30/1.21  fof(f22,plain,(
% 6.30/1.21    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.30/1.21    inference(ennf_transformation,[],[f8])).
% 6.30/1.21  fof(f8,axiom,(
% 6.30/1.21    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.30/1.21  fof(f61,plain,(
% 6.30/1.21    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 6.30/1.21    inference(definition_unfolding,[],[f36,f38,f38])).
% 6.30/1.21  fof(f36,plain,(
% 6.30/1.21    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.30/1.21    inference(cnf_transformation,[],[f2])).
% 6.30/1.21  fof(f2,axiom,(
% 6.30/1.21    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.30/1.21  fof(f6405,plain,(
% 6.30/1.21    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK2) | ~spl4_61),
% 6.30/1.21    inference(superposition,[],[f2790,f1415])).
% 6.30/1.21  fof(f1415,plain,(
% 6.30/1.21    sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~spl4_61),
% 6.30/1.21    inference(avatar_component_clause,[],[f1413])).
% 6.30/1.21  fof(f2790,plain,(
% 6.30/1.21    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X1),X0)) )),
% 6.30/1.21    inference(resolution,[],[f387,f115])).
% 6.30/1.21  fof(f115,plain,(
% 6.30/1.21    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 6.30/1.21    inference(resolution,[],[f56,f63])).
% 6.30/1.21  fof(f63,plain,(
% 6.30/1.21    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.30/1.21    inference(equality_resolution,[],[f49])).
% 6.30/1.21  fof(f49,plain,(
% 6.30/1.21    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.30/1.21    inference(cnf_transformation,[],[f3])).
% 6.30/1.21  fof(f3,axiom,(
% 6.30/1.21    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.30/1.21  fof(f56,plain,(
% 6.30/1.21    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 6.30/1.21    inference(cnf_transformation,[],[f25])).
% 6.30/1.21  fof(f25,plain,(
% 6.30/1.21    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 6.30/1.21    inference(ennf_transformation,[],[f5])).
% 6.30/1.21  fof(f5,axiom,(
% 6.30/1.21    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 6.30/1.21  fof(f387,plain,(
% 6.30/1.21    ( ! [X35,X36,X34] : (~r1_xboole_0(k4_xboole_0(k2_xboole_0(X34,X35),X36),X35) | r1_tarski(k4_xboole_0(k2_xboole_0(X34,X35),X36),X34)) )),
% 6.30/1.21    inference(resolution,[],[f59,f35])).
% 6.30/1.21  fof(f35,plain,(
% 6.30/1.21    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.30/1.21    inference(cnf_transformation,[],[f9])).
% 6.30/1.21  fof(f9,axiom,(
% 6.30/1.21    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.30/1.21  fof(f59,plain,(
% 6.30/1.21    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) )),
% 6.30/1.21    inference(cnf_transformation,[],[f29])).
% 6.30/1.21  fof(f29,plain,(
% 6.30/1.21    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.30/1.21    inference(flattening,[],[f28])).
% 6.30/1.21  fof(f28,plain,(
% 6.30/1.21    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 6.30/1.21    inference(ennf_transformation,[],[f13])).
% 6.30/1.21  fof(f13,axiom,(
% 6.30/1.21    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 6.30/1.21  fof(f6356,plain,(
% 6.30/1.21    ~spl4_15 | spl4_61 | ~spl4_49),
% 6.30/1.21    inference(avatar_split_clause,[],[f6317,f1216,f1413,f334])).
% 6.30/1.21  fof(f334,plain,(
% 6.30/1.21    spl4_15 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 6.30/1.21  fof(f1216,plain,(
% 6.30/1.21    spl4_49 <=> sK0 = k2_xboole_0(sK2,k3_subset_1(sK0,sK1))),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 6.30/1.21  fof(f6317,plain,(
% 6.30/1.21    sK0 = k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_49),
% 6.30/1.21    inference(superposition,[],[f1218,f47])).
% 6.30/1.21  fof(f47,plain,(
% 6.30/1.21    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.30/1.21    inference(cnf_transformation,[],[f24])).
% 6.30/1.21  fof(f24,plain,(
% 6.30/1.21    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.30/1.21    inference(ennf_transformation,[],[f16])).
% 6.30/1.21  fof(f16,axiom,(
% 6.30/1.21    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 6.30/1.21  fof(f1218,plain,(
% 6.30/1.21    sK0 = k2_xboole_0(sK2,k3_subset_1(sK0,sK1)) | ~spl4_49),
% 6.30/1.21    inference(avatar_component_clause,[],[f1216])).
% 6.30/1.21  fof(f6315,plain,(
% 6.30/1.21    spl4_49 | ~spl4_50 | ~spl4_14),
% 6.30/1.21    inference(avatar_split_clause,[],[f6311,f329,f1220,f1216])).
% 6.30/1.21  fof(f1220,plain,(
% 6.30/1.21    spl4_50 <=> r1_tarski(k2_xboole_0(sK2,k3_subset_1(sK0,sK1)),sK0)),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 6.30/1.21  fof(f329,plain,(
% 6.30/1.21    spl4_14 <=> r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1))),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 6.30/1.21  fof(f6311,plain,(
% 6.30/1.21    ~r1_tarski(k2_xboole_0(sK2,k3_subset_1(sK0,sK1)),sK0) | sK0 = k2_xboole_0(sK2,k3_subset_1(sK0,sK1)) | ~spl4_14),
% 6.30/1.21    inference(resolution,[],[f6274,f50])).
% 6.30/1.21  fof(f50,plain,(
% 6.30/1.21    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 6.30/1.21    inference(cnf_transformation,[],[f3])).
% 6.30/1.21  fof(f6274,plain,(
% 6.30/1.21    r1_tarski(sK0,k2_xboole_0(sK2,k3_subset_1(sK0,sK1))) | ~spl4_14),
% 6.30/1.21    inference(resolution,[],[f331,f58])).
% 6.30/1.21  fof(f58,plain,(
% 6.30/1.21    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 6.30/1.21    inference(cnf_transformation,[],[f27])).
% 6.30/1.21  fof(f27,plain,(
% 6.30/1.21    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 6.30/1.21    inference(ennf_transformation,[],[f11])).
% 6.30/1.21  fof(f11,axiom,(
% 6.30/1.21    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 6.30/1.21  fof(f331,plain,(
% 6.30/1.21    r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl4_14),
% 6.30/1.21    inference(avatar_component_clause,[],[f329])).
% 6.30/1.21  fof(f6265,plain,(
% 6.30/1.21    ~spl4_12 | spl4_14 | ~spl4_2),
% 6.30/1.21    inference(avatar_split_clause,[],[f6263,f72,f329,f320])).
% 6.30/1.21  fof(f320,plain,(
% 6.30/1.21    spl4_12 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 6.30/1.21  fof(f72,plain,(
% 6.30/1.21    spl4_2 <=> r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1))),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 6.30/1.21  fof(f6263,plain,(
% 6.30/1.21    r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl4_2),
% 6.30/1.21    inference(superposition,[],[f73,f47])).
% 6.30/1.21  fof(f73,plain,(
% 6.30/1.21    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl4_2),
% 6.30/1.21    inference(avatar_component_clause,[],[f72])).
% 6.30/1.21  fof(f6157,plain,(
% 6.30/1.21    ~spl4_4 | spl4_60),
% 6.30/1.21    inference(avatar_contradiction_clause,[],[f6137])).
% 6.30/1.21  fof(f6137,plain,(
% 6.30/1.21    $false | (~spl4_4 | spl4_60)),
% 6.30/1.21    inference(subsumption_resolution,[],[f1403,f5502])).
% 6.30/1.21  fof(f5502,plain,(
% 6.30/1.21    ( ! [X121] : (r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,X121)),sK0)) ) | ~spl4_4),
% 6.30/1.21    inference(superposition,[],[f3222,f4936])).
% 6.30/1.21  fof(f4936,plain,(
% 6.30/1.21    ( ! [X2,X1] : (k2_xboole_0(X1,k4_xboole_0(X1,X2)) = X1) )),
% 6.30/1.21    inference(resolution,[],[f221,f113])).
% 6.30/1.21  fof(f113,plain,(
% 6.30/1.21    ( ! [X4,X2,X3] : (r1_tarski(k4_xboole_0(k4_xboole_0(X2,X3),X4),X2)) )),
% 6.30/1.21    inference(resolution,[],[f55,f35])).
% 6.30/1.21  fof(f55,plain,(
% 6.30/1.21    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 6.30/1.21    inference(cnf_transformation,[],[f25])).
% 6.30/1.21  fof(f221,plain,(
% 6.30/1.21    ( ! [X8,X9] : (~r1_tarski(k4_xboole_0(X9,X8),X8) | k2_xboole_0(X8,X9) = X8) )),
% 6.30/1.21    inference(superposition,[],[f106,f40])).
% 6.30/1.21  fof(f40,plain,(
% 6.30/1.21    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.30/1.21    inference(cnf_transformation,[],[f10])).
% 6.30/1.21  fof(f10,axiom,(
% 6.30/1.21    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 6.30/1.21  fof(f106,plain,(
% 6.30/1.21    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) )),
% 6.30/1.21    inference(superposition,[],[f46,f37])).
% 6.30/1.21  fof(f37,plain,(
% 6.30/1.21    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 6.30/1.21    inference(cnf_transformation,[],[f1])).
% 6.30/1.21  fof(f1,axiom,(
% 6.30/1.21    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 6.30/1.21  fof(f46,plain,(
% 6.30/1.21    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 6.30/1.21    inference(cnf_transformation,[],[f23])).
% 6.30/1.21  fof(f23,plain,(
% 6.30/1.21    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 6.30/1.21    inference(ennf_transformation,[],[f7])).
% 6.30/1.21  fof(f7,axiom,(
% 6.30/1.21    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 6.30/1.21  fof(f3222,plain,(
% 6.30/1.21    ( ! [X2] : (r1_tarski(k2_xboole_0(sK2,X2),k2_xboole_0(sK0,X2))) ) | ~spl4_4),
% 6.30/1.21    inference(superposition,[],[f2957,f37])).
% 6.30/1.21  fof(f2957,plain,(
% 6.30/1.21    ( ! [X0] : (r1_tarski(k2_xboole_0(sK2,X0),k2_xboole_0(X0,sK0))) ) | ~spl4_4),
% 6.30/1.21    inference(resolution,[],[f2816,f58])).
% 6.30/1.21  fof(f2816,plain,(
% 6.30/1.21    ( ! [X27] : (r1_tarski(k4_xboole_0(k2_xboole_0(sK2,X27),X27),sK0)) ) | ~spl4_4),
% 6.30/1.21    inference(resolution,[],[f2790,f546])).
% 6.30/1.21  fof(f546,plain,(
% 6.30/1.21    ( ! [X60] : (~r1_tarski(X60,sK2) | r1_tarski(X60,sK0)) ) | ~spl4_4),
% 6.30/1.21    inference(resolution,[],[f119,f104])).
% 6.30/1.21  fof(f104,plain,(
% 6.30/1.21    r1_tarski(sK2,sK0) | ~spl4_4),
% 6.30/1.21    inference(resolution,[],[f93,f65])).
% 6.30/1.21  fof(f65,plain,(
% 6.30/1.21    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 6.30/1.21    inference(equality_resolution,[],[f52])).
% 6.30/1.21  fof(f52,plain,(
% 6.30/1.21    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 6.30/1.21    inference(cnf_transformation,[],[f14])).
% 6.30/1.21  fof(f14,axiom,(
% 6.30/1.21    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 6.30/1.21  fof(f93,plain,(
% 6.30/1.21    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl4_4),
% 6.30/1.21    inference(avatar_component_clause,[],[f91])).
% 6.30/1.21  fof(f91,plain,(
% 6.30/1.21    spl4_4 <=> r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 6.30/1.21  fof(f119,plain,(
% 6.30/1.21    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 6.30/1.21    inference(superposition,[],[f57,f46])).
% 6.30/1.21  fof(f57,plain,(
% 6.30/1.21    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 6.30/1.21    inference(cnf_transformation,[],[f26])).
% 6.30/1.21  fof(f26,plain,(
% 6.30/1.21    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 6.30/1.21    inference(ennf_transformation,[],[f6])).
% 6.30/1.21  fof(f6,axiom,(
% 6.30/1.21    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 6.30/1.21  fof(f1403,plain,(
% 6.30/1.21    ~r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK0) | spl4_60),
% 6.30/1.21    inference(avatar_component_clause,[],[f1401])).
% 6.30/1.21  fof(f1401,plain,(
% 6.30/1.21    spl4_60 <=> r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK0)),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_60])])).
% 6.30/1.21  fof(f6156,plain,(
% 6.30/1.21    ~spl4_1 | ~spl4_4 | spl4_61),
% 6.30/1.21    inference(avatar_contradiction_clause,[],[f6139])).
% 6.30/1.21  fof(f6139,plain,(
% 6.30/1.21    $false | (~spl4_1 | ~spl4_4 | spl4_61)),
% 6.30/1.21    inference(unit_resulting_resolution,[],[f1414,f2592,f5502,f50])).
% 6.30/1.21  fof(f2592,plain,(
% 6.30/1.21    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(sK2,k4_xboole_0(X0,sK1)))) ) | ~spl4_1),
% 6.30/1.21    inference(forward_demodulation,[],[f2581,f37])).
% 6.30/1.21  fof(f2581,plain,(
% 6.30/1.21    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(k4_xboole_0(X0,sK1),sK2))) ) | ~spl4_1),
% 6.30/1.21    inference(resolution,[],[f2443,f58])).
% 6.30/1.21  fof(f2443,plain,(
% 6.30/1.21    ( ! [X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,sK1)),sK2)) ) | ~spl4_1),
% 6.30/1.21    inference(resolution,[],[f2258,f457])).
% 6.30/1.21  fof(f457,plain,(
% 6.30/1.21    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X4)) )),
% 6.30/1.21    inference(superposition,[],[f35,f61])).
% 6.30/1.21  fof(f2258,plain,(
% 6.30/1.21    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,sK2)) ) | ~spl4_1),
% 6.30/1.21    inference(resolution,[],[f69,f119])).
% 6.30/1.21  fof(f69,plain,(
% 6.30/1.21    r1_tarski(sK1,sK2) | ~spl4_1),
% 6.30/1.21    inference(avatar_component_clause,[],[f68])).
% 6.30/1.21  fof(f1414,plain,(
% 6.30/1.21    sK0 != k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | spl4_61),
% 6.30/1.21    inference(avatar_component_clause,[],[f1413])).
% 6.30/1.21  fof(f3186,plain,(
% 6.30/1.21    ~spl4_15 | ~spl4_60 | spl4_50),
% 6.30/1.21    inference(avatar_split_clause,[],[f3183,f1220,f1401,f334])).
% 6.30/1.21  fof(f3183,plain,(
% 6.30/1.21    ~r1_tarski(k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_50),
% 6.30/1.21    inference(superposition,[],[f1222,f47])).
% 6.30/1.21  fof(f1222,plain,(
% 6.30/1.21    ~r1_tarski(k2_xboole_0(sK2,k3_subset_1(sK0,sK1)),sK0) | spl4_50),
% 6.30/1.21    inference(avatar_component_clause,[],[f1220])).
% 6.30/1.21  fof(f3168,plain,(
% 6.30/1.21    ~spl4_15 | ~spl4_61 | spl4_49),
% 6.30/1.21    inference(avatar_split_clause,[],[f3165,f1216,f1413,f334])).
% 6.30/1.21  fof(f3165,plain,(
% 6.30/1.21    sK0 != k2_xboole_0(sK2,k4_xboole_0(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_49),
% 6.30/1.21    inference(superposition,[],[f1217,f47])).
% 6.30/1.21  fof(f1217,plain,(
% 6.30/1.21    sK0 != k2_xboole_0(sK2,k3_subset_1(sK0,sK1)) | spl4_49),
% 6.30/1.21    inference(avatar_component_clause,[],[f1216])).
% 6.30/1.21  fof(f3115,plain,(
% 6.30/1.21    spl4_14 | ~spl4_49),
% 6.30/1.21    inference(avatar_contradiction_clause,[],[f3109])).
% 6.30/1.21  fof(f3109,plain,(
% 6.30/1.21    $false | (spl4_14 | ~spl4_49)),
% 6.30/1.21    inference(subsumption_resolution,[],[f330,f2882])).
% 6.30/1.21  fof(f2882,plain,(
% 6.30/1.21    r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | ~spl4_49),
% 6.30/1.21    inference(superposition,[],[f2819,f1218])).
% 6.30/1.21  fof(f2819,plain,(
% 6.30/1.21    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(k2_xboole_0(X5,X4),X5),X4)) )),
% 6.30/1.21    inference(superposition,[],[f2790,f37])).
% 6.30/1.21  fof(f330,plain,(
% 6.30/1.21    ~r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | spl4_14),
% 6.30/1.21    inference(avatar_component_clause,[],[f329])).
% 6.30/1.21  fof(f2401,plain,(
% 6.30/1.21    ~spl4_5 | spl4_100),
% 6.30/1.21    inference(avatar_contradiction_clause,[],[f2390])).
% 6.30/1.21  fof(f2390,plain,(
% 6.30/1.21    $false | (~spl4_5 | spl4_100)),
% 6.30/1.21    inference(subsumption_resolution,[],[f110,f2378])).
% 6.30/1.21  fof(f2378,plain,(
% 6.30/1.21    ~r1_tarski(sK1,sK0) | spl4_100),
% 6.30/1.21    inference(avatar_component_clause,[],[f2376])).
% 6.30/1.21  fof(f110,plain,(
% 6.30/1.21    r1_tarski(sK1,sK0) | ~spl4_5),
% 6.30/1.21    inference(resolution,[],[f98,f65])).
% 6.30/1.21  fof(f98,plain,(
% 6.30/1.21    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_5),
% 6.30/1.21    inference(avatar_component_clause,[],[f96])).
% 6.30/1.21  fof(f96,plain,(
% 6.30/1.21    spl4_5 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 6.30/1.21  fof(f2266,plain,(
% 6.30/1.21    ~spl4_12 | ~spl4_14 | spl4_2),
% 6.30/1.21    inference(avatar_split_clause,[],[f2264,f72,f329,f320])).
% 6.30/1.21  fof(f2264,plain,(
% 6.30/1.21    ~r1_tarski(k4_xboole_0(sK0,sK2),k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl4_2),
% 6.30/1.21    inference(superposition,[],[f74,f47])).
% 6.30/1.21  fof(f74,plain,(
% 6.30/1.21    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | spl4_2),
% 6.30/1.21    inference(avatar_component_clause,[],[f72])).
% 6.30/1.21  fof(f358,plain,(
% 6.30/1.21    spl4_15),
% 6.30/1.21    inference(avatar_contradiction_clause,[],[f354])).
% 6.30/1.21  fof(f354,plain,(
% 6.30/1.21    $false | spl4_15),
% 6.30/1.21    inference(subsumption_resolution,[],[f33,f336])).
% 6.30/1.21  fof(f336,plain,(
% 6.30/1.21    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_15),
% 6.30/1.21    inference(avatar_component_clause,[],[f334])).
% 6.30/1.21  fof(f33,plain,(
% 6.30/1.21    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 6.30/1.21    inference(cnf_transformation,[],[f20])).
% 6.30/1.21  fof(f20,plain,(
% 6.30/1.21    ? [X0,X1] : (? [X2] : ((r1_tarski(X1,X2) <~> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.30/1.21    inference(ennf_transformation,[],[f19])).
% 6.30/1.21  fof(f19,negated_conjecture,(
% 6.30/1.21    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 6.30/1.21    inference(negated_conjecture,[],[f18])).
% 6.30/1.21  fof(f18,conjecture,(
% 6.30/1.21    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 6.30/1.21  fof(f351,plain,(
% 6.30/1.21    spl4_12),
% 6.30/1.21    inference(avatar_contradiction_clause,[],[f347])).
% 6.30/1.21  fof(f347,plain,(
% 6.30/1.21    $false | spl4_12),
% 6.30/1.21    inference(subsumption_resolution,[],[f32,f322])).
% 6.30/1.21  fof(f322,plain,(
% 6.30/1.21    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl4_12),
% 6.30/1.21    inference(avatar_component_clause,[],[f320])).
% 6.30/1.21  fof(f32,plain,(
% 6.30/1.21    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 6.30/1.21    inference(cnf_transformation,[],[f20])).
% 6.30/1.21  fof(f103,plain,(
% 6.30/1.21    ~spl4_3),
% 6.30/1.21    inference(avatar_contradiction_clause,[],[f100])).
% 6.30/1.21  fof(f100,plain,(
% 6.30/1.21    $false | ~spl4_3),
% 6.30/1.21    inference(unit_resulting_resolution,[],[f34,f89])).
% 6.30/1.21  fof(f89,plain,(
% 6.30/1.21    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_3),
% 6.30/1.21    inference(avatar_component_clause,[],[f87])).
% 6.30/1.21  fof(f87,plain,(
% 6.30/1.21    spl4_3 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 6.30/1.21    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 6.30/1.21  fof(f34,plain,(
% 6.30/1.21    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 6.30/1.21    inference(cnf_transformation,[],[f17])).
% 6.30/1.21  fof(f17,axiom,(
% 6.30/1.21    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 6.30/1.21  fof(f99,plain,(
% 6.30/1.21    spl4_3 | spl4_5),
% 6.30/1.21    inference(avatar_split_clause,[],[f84,f96,f87])).
% 6.30/1.21  fof(f84,plain,(
% 6.30/1.21    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 6.30/1.21    inference(resolution,[],[f44,f33])).
% 6.30/1.21  fof(f44,plain,(
% 6.30/1.21    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 6.30/1.21    inference(cnf_transformation,[],[f21])).
% 6.30/1.21  fof(f21,plain,(
% 6.30/1.21    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 6.30/1.21    inference(ennf_transformation,[],[f15])).
% 6.30/1.21  fof(f15,axiom,(
% 6.30/1.21    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 6.30/1.21    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 6.30/1.21  fof(f94,plain,(
% 6.30/1.21    spl4_3 | spl4_4),
% 6.30/1.21    inference(avatar_split_clause,[],[f83,f91,f87])).
% 6.30/1.21  fof(f83,plain,(
% 6.30/1.21    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 6.30/1.21    inference(resolution,[],[f44,f32])).
% 6.30/1.21  fof(f76,plain,(
% 6.30/1.21    spl4_1 | spl4_2),
% 6.30/1.21    inference(avatar_split_clause,[],[f30,f72,f68])).
% 6.30/1.21  fof(f30,plain,(
% 6.30/1.21    r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | r1_tarski(sK1,sK2)),
% 6.30/1.21    inference(cnf_transformation,[],[f20])).
% 6.30/1.21  fof(f75,plain,(
% 6.30/1.21    ~spl4_1 | ~spl4_2),
% 6.30/1.21    inference(avatar_split_clause,[],[f31,f72,f68])).
% 6.30/1.21  fof(f31,plain,(
% 6.30/1.21    ~r1_tarski(k3_subset_1(sK0,sK2),k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,sK2)),
% 6.30/1.21    inference(cnf_transformation,[],[f20])).
% 6.30/1.21  % SZS output end Proof for theBenchmark
% 6.30/1.21  % (2024)------------------------------
% 6.30/1.21  % (2024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.30/1.21  % (2024)Termination reason: Refutation
% 6.30/1.21  
% 6.30/1.21  % (2024)Memory used [KB]: 11513
% 6.30/1.21  % (2024)Time elapsed: 0.766 s
% 6.30/1.21  % (2024)------------------------------
% 6.30/1.21  % (2024)------------------------------
% 6.30/1.22  % (2001)Success in time 0.843 s
%------------------------------------------------------------------------------
