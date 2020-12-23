%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:58 EST 2020

% Result     : Theorem 13.63s
% Output     : Refutation 13.63s
% Verified   : 
% Statistics : Number of formulae       :  187 ( 472 expanded)
%              Number of leaves         :   38 ( 167 expanded)
%              Depth                    :   14
%              Number of atoms          :  397 ( 905 expanded)
%              Number of equality atoms :   57 ( 236 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (13068)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
fof(f24004,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f597,f602,f609,f736,f2097,f2101,f3432,f3447,f6678,f6801,f6931,f7089,f7866,f7873,f7884,f9275,f9455,f23845,f23963,f24003])).

fof(f24003,plain,(
    spl4_199 ),
    inference(avatar_contradiction_clause,[],[f23977])).

fof(f23977,plain,
    ( $false
    | spl4_199 ),
    inference(unit_resulting_resolution,[],[f61,f3067,f23962,f1105])).

fof(f1105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(k4_xboole_0(X3,X0),X2)
      | r1_tarski(X3,X0)
      | ~ r1_tarski(k2_xboole_0(X1,X2),X0) ) ),
    inference(superposition,[],[f203,f92])).

fof(f92,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f45,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f45,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
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

fof(f203,plain,(
    ! [X14,X12,X13,X11] :
      ( r1_tarski(X11,k2_xboole_0(X12,k2_xboole_0(X13,X14)))
      | ~ r1_tarski(k4_xboole_0(X11,X12),X14) ) ),
    inference(resolution,[],[f58,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f23962,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | spl4_199 ),
    inference(avatar_component_clause,[],[f23960])).

fof(f23960,plain,
    ( spl4_199
  <=> r1_tarski(sK1,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_199])])).

fof(f3067,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X5,k2_xboole_0(X5,X4)),X4) ),
    inference(superposition,[],[f3032,f38])).

fof(f3032,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k2_xboole_0(X0,X1)),X0) ),
    inference(superposition,[],[f2947,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2947,plain,(
    ! [X10,X11,X9] : r1_tarski(k4_xboole_0(X9,k2_xboole_0(X11,k4_xboole_0(X9,X10))),X10) ),
    inference(superposition,[],[f2471,f38])).

fof(f2471,plain,(
    ! [X28,X26,X27] : r1_tarski(k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X27,X26),X28)),X26) ),
    inference(forward_demodulation,[],[f2341,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f2341,plain,(
    ! [X28,X26,X27] : r1_tarski(k4_xboole_0(k4_xboole_0(X27,k4_xboole_0(X27,X26)),X28),X26) ),
    inference(superposition,[],[f36,f391])).

fof(f391,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k2_xboole_0(k4_xboole_0(X4,X5),X6)) = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X6) ),
    inference(superposition,[],[f56,f60])).

fof(f60,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f37,f39,f39])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f23963,plain,
    ( ~ spl4_10
    | ~ spl4_12
    | ~ spl4_199
    | spl4_9
    | ~ spl4_138 ),
    inference(avatar_split_clause,[],[f23958,f9272,f255,f23960,f585,f260])).

fof(f260,plain,
    ( spl4_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f585,plain,
    ( spl4_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f255,plain,
    ( spl4_9
  <=> r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f9272,plain,
    ( spl4_138
  <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).

fof(f23958,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_9
    | ~ spl4_138 ),
    inference(superposition,[],[f23942,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f23942,plain,
    ( ~ r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2))
    | spl4_9
    | ~ spl4_138 ),
    inference(resolution,[],[f23875,f659])).

fof(f659,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k4_xboole_0(X5,X4),k4_xboole_0(X5,X3))
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f346,f45])).

fof(f346,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1)) ),
    inference(superposition,[],[f36,f56])).

fof(f23875,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1))
    | spl4_9
    | ~ spl4_138 ),
    inference(forward_demodulation,[],[f257,f9274])).

fof(f9274,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ spl4_138 ),
    inference(avatar_component_clause,[],[f9272])).

fof(f257,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    | spl4_9 ),
    inference(avatar_component_clause,[],[f255])).

fof(f23845,plain,
    ( ~ spl4_2
    | spl4_23
    | ~ spl4_41
    | ~ spl4_96 ),
    inference(avatar_contradiction_clause,[],[f23805])).

fof(f23805,plain,
    ( $false
    | ~ spl4_2
    | spl4_23
    | ~ spl4_41
    | ~ spl4_96 ),
    inference(unit_resulting_resolution,[],[f88,f735,f10543])).

fof(f10543,plain,
    ( ! [X1] :
        ( r1_tarski(k2_xboole_0(sK1,X1),sK0)
        | ~ r1_tarski(X1,sK0) )
    | ~ spl4_41
    | ~ spl4_96 ),
    inference(superposition,[],[f9810,f45])).

fof(f9810,plain,
    ( ! [X2] : r1_tarski(k2_xboole_0(sK1,X2),k2_xboole_0(X2,sK0))
    | ~ spl4_41
    | ~ spl4_96 ),
    inference(superposition,[],[f8675,f38])).

fof(f8675,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0))
    | ~ spl4_41
    | ~ spl4_96 ),
    inference(resolution,[],[f8415,f58])).

fof(f8415,plain,
    ( ! [X17] : r1_tarski(k4_xboole_0(k2_xboole_0(X17,sK1),X17),sK0)
    | ~ spl4_41
    | ~ spl4_96 ),
    inference(resolution,[],[f8257,f7903])).

fof(f7903,plain,
    ( ! [X8] :
        ( ~ r1_tarski(X8,sK1)
        | r1_tarski(X8,sK0) )
    | ~ spl4_96 ),
    inference(superposition,[],[f57,f7198])).

fof(f7198,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl4_96 ),
    inference(avatar_component_clause,[],[f7196])).

fof(f7196,plain,
    ( spl4_96
  <=> sK0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).

fof(f8257,plain,
    ( ! [X19,X18] : r1_tarski(k4_xboole_0(k2_xboole_0(X18,X19),X18),X19)
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f8200,f5536])).

fof(f5536,plain,
    ( ! [X4] : k2_xboole_0(X4,k1_xboole_0) = X4
    | ~ spl4_41 ),
    inference(superposition,[],[f5473,f3457])).

fof(f3457,plain,
    ( ! [X8] : k2_xboole_0(X8,X8) = k2_xboole_0(X8,k1_xboole_0)
    | ~ spl4_41 ),
    inference(superposition,[],[f40,f3427])).

fof(f3427,plain,
    ( ! [X10] : k1_xboole_0 = k4_xboole_0(X10,X10)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f3426])).

fof(f3426,plain,
    ( spl4_41
  <=> ! [X10] : k1_xboole_0 = k4_xboole_0(X10,X10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f5473,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f110,f36])).

fof(f110,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X3,X2),X2)
      | k2_xboole_0(X2,X3) = X2 ) ),
    inference(superposition,[],[f40,f92])).

fof(f8200,plain,
    ( ! [X19,X18] : r1_tarski(k4_xboole_0(k2_xboole_0(X18,X19),k2_xboole_0(X18,k1_xboole_0)),X19)
    | ~ spl4_41 ),
    inference(superposition,[],[f436,f3427])).

fof(f436,plain,(
    ! [X8,X7,X9] : r1_tarski(k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,X9)))),X9) ),
    inference(forward_demodulation,[],[f427,f56])).

fof(f427,plain,(
    ! [X8,X7,X9] : r1_tarski(k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X9))),X9) ),
    inference(superposition,[],[f389,f56])).

fof(f389,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f36,f60])).

fof(f735,plain,
    ( ~ r1_tarski(k2_xboole_0(sK1,sK2),sK0)
    | spl4_23 ),
    inference(avatar_component_clause,[],[f733])).

fof(f733,plain,
    ( spl4_23
  <=> r1_tarski(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f88,plain,
    ( r1_tarski(sK2,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f81,f63])).

fof(f63,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f81,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_2
  <=> r2_hidden(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f9455,plain,(
    spl4_137 ),
    inference(avatar_contradiction_clause,[],[f9447])).

fof(f9447,plain,
    ( $false
    | spl4_137 ),
    inference(unit_resulting_resolution,[],[f34,f36,f9270,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X0) ) ),
    inference(resolution,[],[f43,f64])).

fof(f64,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f9270,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | spl4_137 ),
    inference(avatar_component_clause,[],[f9268])).

fof(f9268,plain,
    ( spl4_137
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_137])])).

fof(f34,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f9275,plain,
    ( ~ spl4_137
    | spl4_138
    | ~ spl4_41
    | ~ spl4_96 ),
    inference(avatar_split_clause,[],[f9225,f7196,f3426,f9272,f9268])).

fof(f9225,plain,
    ( k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)
    | ~ m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl4_41
    | ~ spl4_96 ),
    inference(superposition,[],[f290,f8050])).

fof(f8050,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_41
    | ~ spl4_96 ),
    inference(forward_demodulation,[],[f8006,f5904])).

fof(f5904,plain,
    ( ! [X7] : k4_xboole_0(X7,k1_xboole_0) = X7
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f5794,f5535])).

fof(f5535,plain,
    ( ! [X3] : k2_xboole_0(k1_xboole_0,X3) = X3
    | ~ spl4_41 ),
    inference(superposition,[],[f5473,f3525])).

fof(f3525,plain,
    ( ! [X3] : k2_xboole_0(X3,X3) = k2_xboole_0(k1_xboole_0,X3)
    | ~ spl4_41 ),
    inference(superposition,[],[f3457,f38])).

fof(f5794,plain,
    ( ! [X7] : k4_xboole_0(X7,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X7)
    | ~ spl4_41 ),
    inference(superposition,[],[f5535,f40])).

fof(f8006,plain,
    ( k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl4_41
    | ~ spl4_96 ),
    inference(superposition,[],[f60,f7948])).

fof(f7948,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl4_41
    | ~ spl4_96 ),
    inference(superposition,[],[f3512,f7198])).

fof(f3512,plain,
    ( ! [X8,X7] : k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,X7))
    | ~ spl4_41 ),
    inference(forward_demodulation,[],[f3451,f40])).

fof(f3451,plain,
    ( ! [X8,X7] : k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8)))
    | ~ spl4_41 ),
    inference(superposition,[],[f3427,f56])).

fof(f290,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f48,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f7884,plain,
    ( spl4_96
    | ~ spl4_63
    | ~ spl4_85 ),
    inference(avatar_split_clause,[],[f7881,f7074,f6781,f7196])).

fof(f6781,plain,
    ( spl4_63
  <=> r1_tarski(sK0,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f7074,plain,
    ( spl4_85
  <=> r1_tarski(k2_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f7881,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl4_85 ),
    inference(resolution,[],[f7076,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f7076,plain,
    ( r1_tarski(k2_xboole_0(sK0,sK1),sK0)
    | ~ spl4_85 ),
    inference(avatar_component_clause,[],[f7074])).

fof(f7873,plain,(
    spl4_125 ),
    inference(avatar_contradiction_clause,[],[f7868])).

fof(f7868,plain,
    ( $false
    | spl4_125 ),
    inference(unit_resulting_resolution,[],[f61,f61,f7865,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | r1_tarski(X2,X0)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f57,f92])).

fof(f7865,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_125 ),
    inference(avatar_component_clause,[],[f7863])).

fof(f7863,plain,
    ( spl4_125
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_125])])).

fof(f7866,plain,
    ( ~ spl4_84
    | ~ spl4_125
    | spl4_85 ),
    inference(avatar_split_clause,[],[f7860,f7074,f7863,f7070])).

fof(f7070,plain,
    ( spl4_84
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f7860,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK1,sK0)
    | spl4_85 ),
    inference(superposition,[],[f7075,f92])).

fof(f7075,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),sK0)
    | spl4_85 ),
    inference(avatar_component_clause,[],[f7074])).

fof(f7089,plain,
    ( ~ spl4_3
    | spl4_84 ),
    inference(avatar_contradiction_clause,[],[f7082])).

fof(f7082,plain,
    ( $false
    | ~ spl4_3
    | spl4_84 ),
    inference(subsumption_resolution,[],[f2102,f7072])).

fof(f7072,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_84 ),
    inference(avatar_component_clause,[],[f7070])).

fof(f2102,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f86,f63])).

fof(f86,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_3
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f6931,plain,
    ( ~ spl4_10
    | ~ spl4_12
    | spl4_51
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f6916,f255,f6675,f585,f260])).

fof(f6675,plain,
    ( spl4_51
  <=> r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).

fof(f6916,plain,
    ( r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl4_9 ),
    inference(superposition,[],[f256,f59])).

fof(f256,plain,
    ( r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f255])).

fof(f6801,plain,(
    spl4_63 ),
    inference(avatar_contradiction_clause,[],[f6789])).

fof(f6789,plain,
    ( $false
    | spl4_63 ),
    inference(unit_resulting_resolution,[],[f214,f61,f6783,f102])).

fof(f6783,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK1))
    | spl4_63 ),
    inference(avatar_component_clause,[],[f6781])).

fof(f214,plain,(
    ! [X4,X5] : r1_tarski(X5,k2_xboole_0(X5,X4)) ),
    inference(superposition,[],[f199,f38])).

fof(f199,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(resolution,[],[f58,f36])).

fof(f6678,plain,
    ( ~ spl4_13
    | ~ spl4_51
    | spl4_14 ),
    inference(avatar_split_clause,[],[f627,f594,f6675,f589])).

fof(f589,plain,
    ( spl4_13
  <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f594,plain,
    ( spl4_14
  <=> r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f627,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_14 ),
    inference(superposition,[],[f596,f47])).

fof(f596,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f594])).

fof(f3447,plain,(
    spl4_42 ),
    inference(avatar_contradiction_clause,[],[f3439])).

fof(f3439,plain,
    ( $false
    | spl4_42 ),
    inference(unit_resulting_resolution,[],[f35,f61,f3431,f102])).

fof(f3431,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | spl4_42 ),
    inference(avatar_component_clause,[],[f3429])).

fof(f3429,plain,
    ( spl4_42
  <=> r1_tarski(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f35,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f3432,plain,
    ( spl4_41
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f3415,f3429,f3426])).

fof(f3415,plain,(
    ! [X10] :
      ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
      | k1_xboole_0 = k4_xboole_0(X10,X10) ) ),
    inference(resolution,[],[f3127,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f51,f35])).

fof(f3127,plain,(
    ! [X0,X1] :
      ( r1_tarski(k4_xboole_0(X1,X1),X0)
      | ~ r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f3092,f92])).

fof(f3092,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X2),k2_xboole_0(X3,X3)) ),
    inference(resolution,[],[f3067,f348])).

fof(f348,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r1_tarski(k4_xboole_0(X6,k2_xboole_0(X7,X8)),X9)
      | r1_tarski(k4_xboole_0(X6,X7),k2_xboole_0(X8,X9)) ) ),
    inference(superposition,[],[f58,f56])).

fof(f2101,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f2098])).

fof(f2098,plain,
    ( $false
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f34,f77])).

fof(f77,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_1
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2097,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f603,f84,f75])).

fof(f603,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f33,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f736,plain,
    ( ~ spl4_23
    | spl4_1
    | spl4_13 ),
    inference(avatar_split_clause,[],[f725,f589,f75,f733])).

fof(f725,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ r1_tarski(k2_xboole_0(sK1,sK2),sK0)
    | spl4_13 ),
    inference(resolution,[],[f70,f591])).

fof(f591,plain,
    ( ~ m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))
    | spl4_13 ),
    inference(avatar_component_clause,[],[f589])).

fof(f609,plain,(
    spl4_12 ),
    inference(avatar_contradiction_clause,[],[f605])).

fof(f605,plain,
    ( $false
    | spl4_12 ),
    inference(subsumption_resolution,[],[f31,f587])).

fof(f587,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f585])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f602,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f598])).

fof(f598,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f33,f262])).

fof(f262,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f260])).

fof(f597,plain,
    ( ~ spl4_10
    | ~ spl4_12
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f583,f594,f585,f260])).

fof(f583,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f32,f59])).

fof(f32,plain,(
    ~ r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f82,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f71,f79,f75])).

fof(f71,plain,
    ( r2_hidden(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f44,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:52:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.51  % (13035)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (13027)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.51  % (13025)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (13022)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.52  % (13043)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (13027)Refutation not found, incomplete strategy% (13027)------------------------------
% 0.20/0.52  % (13027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (13027)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (13027)Memory used [KB]: 10746
% 0.20/0.52  % (13027)Time elapsed: 0.100 s
% 0.20/0.52  % (13027)------------------------------
% 0.20/0.52  % (13027)------------------------------
% 0.20/0.52  % (13038)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (13031)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (13021)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (13037)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.52  % (13018)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (13046)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (13046)Refutation not found, incomplete strategy% (13046)------------------------------
% 0.20/0.53  % (13046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13046)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13046)Memory used [KB]: 1663
% 0.20/0.53  % (13046)Time elapsed: 0.001 s
% 0.20/0.53  % (13046)------------------------------
% 0.20/0.53  % (13046)------------------------------
% 0.20/0.53  % (13020)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (13017)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.53  % (13045)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.53  % (13030)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (13019)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (13045)Refutation not found, incomplete strategy% (13045)------------------------------
% 0.20/0.53  % (13045)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (13045)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (13045)Memory used [KB]: 10746
% 0.20/0.53  % (13045)Time elapsed: 0.122 s
% 0.20/0.53  % (13045)------------------------------
% 0.20/0.53  % (13045)------------------------------
% 0.20/0.53  % (13023)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (13029)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (13026)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.54  % (13039)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.54  % (13036)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (13032)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.54  % (13028)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.54  % (13033)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.55  % (13042)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.55  % (13024)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (13033)Refutation not found, incomplete strategy% (13033)------------------------------
% 0.20/0.55  % (13033)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (13033)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (13033)Memory used [KB]: 10618
% 0.20/0.55  % (13033)Time elapsed: 0.149 s
% 0.20/0.55  % (13033)------------------------------
% 0.20/0.55  % (13033)------------------------------
% 0.20/0.55  % (13044)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.55  % (13040)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.55  % (13034)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.55  % (13041)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.15/0.66  % (13048)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.15/0.67  % (13049)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.70/0.71  % (13050)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.70/0.72  % (13020)Refutation not found, incomplete strategy% (13020)------------------------------
% 2.70/0.72  % (13020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.72  % (13020)Termination reason: Refutation not found, incomplete strategy
% 2.70/0.72  
% 2.70/0.72  % (13020)Memory used [KB]: 6396
% 2.70/0.72  % (13020)Time elapsed: 0.302 s
% 2.70/0.72  % (13020)------------------------------
% 2.70/0.72  % (13020)------------------------------
% 2.70/0.77  % (13051)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.22/0.82  % (13019)Time limit reached!
% 3.22/0.82  % (13019)------------------------------
% 3.22/0.82  % (13019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.82  % (13019)Termination reason: Time limit
% 3.22/0.82  
% 3.22/0.82  % (13019)Memory used [KB]: 6524
% 3.22/0.82  % (13019)Time elapsed: 0.415 s
% 3.22/0.82  % (13019)------------------------------
% 3.22/0.82  % (13019)------------------------------
% 3.22/0.83  % (13041)Time limit reached!
% 3.22/0.83  % (13041)------------------------------
% 3.22/0.83  % (13041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.22/0.83  % (13041)Termination reason: Time limit
% 3.22/0.83  % (13041)Termination phase: Saturation
% 3.22/0.83  
% 3.22/0.83  % (13041)Memory used [KB]: 13432
% 3.22/0.83  % (13041)Time elapsed: 0.400 s
% 3.22/0.83  % (13041)------------------------------
% 3.22/0.83  % (13041)------------------------------
% 3.97/0.89  % (13052)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.41/0.95  % (13023)Time limit reached!
% 4.41/0.95  % (13023)------------------------------
% 4.41/0.95  % (13023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.95  % (13023)Termination reason: Time limit
% 4.41/0.95  
% 4.41/0.95  % (13023)Memory used [KB]: 14967
% 4.41/0.95  % (13023)Time elapsed: 0.512 s
% 4.41/0.95  % (13023)------------------------------
% 4.41/0.95  % (13023)------------------------------
% 4.41/0.95  % (13053)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.41/0.96  % (13031)Time limit reached!
% 4.41/0.96  % (13031)------------------------------
% 4.41/0.96  % (13031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.41/0.96  % (13031)Termination reason: Time limit
% 4.41/0.96  
% 4.41/0.96  % (13031)Memory used [KB]: 5884
% 4.41/0.96  % (13031)Time elapsed: 0.519 s
% 4.41/0.96  % (13031)------------------------------
% 4.41/0.96  % (13031)------------------------------
% 4.41/0.97  % (13054)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.93/1.00  % (13024)Time limit reached!
% 4.93/1.00  % (13024)------------------------------
% 4.93/1.00  % (13024)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.00  % (13024)Termination reason: Time limit
% 4.93/1.00  % (13024)Termination phase: Saturation
% 4.93/1.00  
% 4.93/1.00  % (13024)Memory used [KB]: 5500
% 4.93/1.00  % (13024)Time elapsed: 0.600 s
% 4.93/1.00  % (13024)------------------------------
% 4.93/1.00  % (13024)------------------------------
% 5.63/1.10  % (13055)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 5.63/1.10  % (13056)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 5.63/1.15  % (13057)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 6.82/1.23  % (13018)Time limit reached!
% 6.82/1.23  % (13018)------------------------------
% 6.82/1.23  % (13018)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.82/1.23  % (13018)Termination reason: Time limit
% 6.82/1.23  
% 6.82/1.23  % (13018)Memory used [KB]: 8443
% 6.82/1.23  % (13018)Time elapsed: 0.827 s
% 6.82/1.23  % (13018)------------------------------
% 6.82/1.23  % (13018)------------------------------
% 7.58/1.37  % (13058)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 7.58/1.38  % (13050)Time limit reached!
% 7.58/1.38  % (13050)------------------------------
% 7.58/1.38  % (13050)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.58/1.38  % (13050)Termination reason: Time limit
% 7.58/1.38  
% 7.58/1.38  % (13050)Memory used [KB]: 9594
% 7.58/1.38  % (13050)Time elapsed: 0.808 s
% 7.58/1.38  % (13050)------------------------------
% 7.58/1.38  % (13050)------------------------------
% 8.14/1.41  % (13044)Time limit reached!
% 8.14/1.41  % (13044)------------------------------
% 8.14/1.41  % (13044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.14/1.41  % (13044)Termination reason: Time limit
% 8.14/1.41  
% 8.14/1.41  % (13044)Memory used [KB]: 14456
% 8.14/1.41  % (13044)Time elapsed: 1.010 s
% 8.14/1.41  % (13044)------------------------------
% 8.14/1.41  % (13044)------------------------------
% 8.14/1.41  % (13029)Time limit reached!
% 8.14/1.41  % (13029)------------------------------
% 8.14/1.41  % (13029)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.14/1.41  % (13029)Termination reason: Time limit
% 8.14/1.41  
% 8.14/1.41  % (13029)Memory used [KB]: 17526
% 8.14/1.41  % (13029)Time elapsed: 1.021 s
% 8.14/1.41  % (13029)------------------------------
% 8.14/1.41  % (13029)------------------------------
% 8.77/1.50  % (13054)Time limit reached!
% 8.77/1.50  % (13054)------------------------------
% 8.77/1.50  % (13054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.77/1.50  % (13054)Termination reason: Time limit
% 8.77/1.50  % (13054)Termination phase: Saturation
% 8.77/1.50  
% 8.77/1.50  % (13054)Memory used [KB]: 17142
% 8.77/1.50  % (13054)Time elapsed: 0.600 s
% 8.77/1.50  % (13054)------------------------------
% 8.77/1.50  % (13054)------------------------------
% 9.09/1.55  % (13060)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 9.09/1.55  % (13061)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 9.09/1.57  % (13059)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 9.76/1.63  % (13017)Time limit reached!
% 9.76/1.63  % (13017)------------------------------
% 9.76/1.63  % (13017)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.76/1.63  % (13017)Termination reason: Time limit
% 9.76/1.63  
% 9.76/1.63  % (13017)Memory used [KB]: 8827
% 9.76/1.63  % (13017)Time elapsed: 1.206 s
% 9.76/1.63  % (13017)------------------------------
% 9.76/1.63  % (13017)------------------------------
% 9.76/1.64  % (13062)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 10.62/1.71  % (13022)Time limit reached!
% 10.62/1.71  % (13022)------------------------------
% 10.62/1.71  % (13022)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.62/1.71  % (13022)Termination reason: Time limit
% 10.62/1.71  
% 10.62/1.71  % (13022)Memory used [KB]: 14583
% 10.62/1.71  % (13022)Time elapsed: 1.305 s
% 10.62/1.71  % (13022)------------------------------
% 10.62/1.71  % (13022)------------------------------
% 11.42/1.81  % (13062)Refutation not found, incomplete strategy% (13062)------------------------------
% 11.42/1.81  % (13062)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.42/1.81  % (13062)Termination reason: Refutation not found, incomplete strategy
% 11.42/1.81  
% 11.42/1.81  % (13062)Memory used [KB]: 6268
% 11.42/1.81  % (13062)Time elapsed: 0.293 s
% 11.42/1.81  % (13062)------------------------------
% 11.42/1.81  % (13062)------------------------------
% 11.49/1.82  % (13063)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 11.49/1.84  % (13057)Time limit reached!
% 11.49/1.84  % (13057)------------------------------
% 11.49/1.84  % (13057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.49/1.84  % (13057)Termination reason: Time limit
% 11.49/1.84  
% 11.49/1.84  % (13057)Memory used [KB]: 17910
% 11.49/1.84  % (13057)Time elapsed: 0.810 s
% 11.49/1.84  % (13057)------------------------------
% 11.49/1.84  % (13057)------------------------------
% 11.49/1.85  % (13064)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 11.49/1.85  % (13061)Time limit reached!
% 11.49/1.85  % (13061)------------------------------
% 11.49/1.85  % (13061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.49/1.85  % (13061)Termination reason: Time limit
% 11.49/1.85  % (13061)Termination phase: Saturation
% 11.49/1.85  
% 11.49/1.86  % (13061)Memory used [KB]: 13432
% 11.49/1.86  % (13061)Time elapsed: 0.400 s
% 11.49/1.86  % (13061)------------------------------
% 11.49/1.86  % (13061)------------------------------
% 12.21/1.97  % (13065)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 12.21/1.98  % (13066)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 12.21/1.99  % (13067)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 12.80/2.01  % (13043)Time limit reached!
% 12.80/2.01  % (13043)------------------------------
% 12.80/2.01  % (13043)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.80/2.01  % (13043)Termination reason: Time limit
% 12.80/2.01  % (13043)Termination phase: Saturation
% 12.80/2.01  
% 12.80/2.01  % (13043)Memory used [KB]: 25330
% 12.80/2.01  % (13043)Time elapsed: 1.600 s
% 12.80/2.01  % (13043)------------------------------
% 12.80/2.01  % (13043)------------------------------
% 13.42/2.08  % (13063)Time limit reached!
% 13.42/2.08  % (13063)------------------------------
% 13.42/2.08  % (13063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.42/2.08  % (13063)Termination reason: Time limit
% 13.42/2.08  
% 13.42/2.08  % (13063)Memory used [KB]: 6524
% 13.42/2.08  % (13063)Time elapsed: 0.432 s
% 13.42/2.08  % (13063)------------------------------
% 13.42/2.08  % (13063)------------------------------
% 13.63/2.13  % (13030)Refutation found. Thanks to Tanya!
% 13.63/2.13  % SZS status Theorem for theBenchmark
% 13.63/2.13  % SZS output start Proof for theBenchmark
% 13.63/2.15  % (13068)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 13.63/2.16  fof(f24004,plain,(
% 13.63/2.16    $false),
% 13.63/2.16    inference(avatar_sat_refutation,[],[f82,f597,f602,f609,f736,f2097,f2101,f3432,f3447,f6678,f6801,f6931,f7089,f7866,f7873,f7884,f9275,f9455,f23845,f23963,f24003])).
% 13.63/2.16  fof(f24003,plain,(
% 13.63/2.16    spl4_199),
% 13.63/2.16    inference(avatar_contradiction_clause,[],[f23977])).
% 13.63/2.16  fof(f23977,plain,(
% 13.63/2.16    $false | spl4_199),
% 13.63/2.16    inference(unit_resulting_resolution,[],[f61,f3067,f23962,f1105])).
% 13.63/2.16  fof(f1105,plain,(
% 13.63/2.16    ( ! [X2,X0,X3,X1] : (~r1_tarski(k4_xboole_0(X3,X0),X2) | r1_tarski(X3,X0) | ~r1_tarski(k2_xboole_0(X1,X2),X0)) )),
% 13.63/2.16    inference(superposition,[],[f203,f92])).
% 13.63/2.16  fof(f92,plain,(
% 13.63/2.16    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) )),
% 13.63/2.16    inference(superposition,[],[f45,f38])).
% 13.63/2.16  fof(f38,plain,(
% 13.63/2.16    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 13.63/2.16    inference(cnf_transformation,[],[f1])).
% 13.63/2.16  fof(f1,axiom,(
% 13.63/2.16    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 13.63/2.16  fof(f45,plain,(
% 13.63/2.16    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 13.63/2.16    inference(cnf_transformation,[],[f23])).
% 13.63/2.16  fof(f23,plain,(
% 13.63/2.16    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 13.63/2.16    inference(ennf_transformation,[],[f5])).
% 13.63/2.16  fof(f5,axiom,(
% 13.63/2.16    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 13.63/2.16  fof(f203,plain,(
% 13.63/2.16    ( ! [X14,X12,X13,X11] : (r1_tarski(X11,k2_xboole_0(X12,k2_xboole_0(X13,X14))) | ~r1_tarski(k4_xboole_0(X11,X12),X14)) )),
% 13.63/2.16    inference(resolution,[],[f58,f57])).
% 13.63/2.16  fof(f57,plain,(
% 13.63/2.16    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 13.63/2.16    inference(cnf_transformation,[],[f27])).
% 13.63/2.16  fof(f27,plain,(
% 13.63/2.16    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 13.63/2.16    inference(ennf_transformation,[],[f4])).
% 13.63/2.16  fof(f4,axiom,(
% 13.63/2.16    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 13.63/2.16  fof(f58,plain,(
% 13.63/2.16    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 13.63/2.16    inference(cnf_transformation,[],[f28])).
% 13.63/2.16  fof(f28,plain,(
% 13.63/2.16    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 13.63/2.16    inference(ennf_transformation,[],[f10])).
% 13.63/2.16  fof(f10,axiom,(
% 13.63/2.16    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 13.63/2.16  fof(f23962,plain,(
% 13.63/2.16    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | spl4_199),
% 13.63/2.16    inference(avatar_component_clause,[],[f23960])).
% 13.63/2.16  fof(f23960,plain,(
% 13.63/2.16    spl4_199 <=> r1_tarski(sK1,k2_xboole_0(sK1,sK2))),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_199])])).
% 13.63/2.16  fof(f3067,plain,(
% 13.63/2.16    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(X5,k2_xboole_0(X5,X4)),X4)) )),
% 13.63/2.16    inference(superposition,[],[f3032,f38])).
% 13.63/2.16  fof(f3032,plain,(
% 13.63/2.16    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k2_xboole_0(X0,X1)),X0)) )),
% 13.63/2.16    inference(superposition,[],[f2947,f40])).
% 13.63/2.16  fof(f40,plain,(
% 13.63/2.16    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 13.63/2.16    inference(cnf_transformation,[],[f8])).
% 13.63/2.16  fof(f8,axiom,(
% 13.63/2.16    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 13.63/2.16  fof(f2947,plain,(
% 13.63/2.16    ( ! [X10,X11,X9] : (r1_tarski(k4_xboole_0(X9,k2_xboole_0(X11,k4_xboole_0(X9,X10))),X10)) )),
% 13.63/2.16    inference(superposition,[],[f2471,f38])).
% 13.63/2.16  fof(f2471,plain,(
% 13.63/2.16    ( ! [X28,X26,X27] : (r1_tarski(k4_xboole_0(X27,k2_xboole_0(k4_xboole_0(X27,X26),X28)),X26)) )),
% 13.63/2.16    inference(forward_demodulation,[],[f2341,f56])).
% 13.63/2.16  fof(f56,plain,(
% 13.63/2.16    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 13.63/2.16    inference(cnf_transformation,[],[f9])).
% 13.63/2.16  fof(f9,axiom,(
% 13.63/2.16    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 13.63/2.16  fof(f2341,plain,(
% 13.63/2.16    ( ! [X28,X26,X27] : (r1_tarski(k4_xboole_0(k4_xboole_0(X27,k4_xboole_0(X27,X26)),X28),X26)) )),
% 13.63/2.16    inference(superposition,[],[f36,f391])).
% 13.63/2.16  fof(f391,plain,(
% 13.63/2.16    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k2_xboole_0(k4_xboole_0(X4,X5),X6)) = k4_xboole_0(k4_xboole_0(X5,k4_xboole_0(X5,X4)),X6)) )),
% 13.63/2.16    inference(superposition,[],[f56,f60])).
% 13.63/2.16  fof(f60,plain,(
% 13.63/2.16    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 13.63/2.16    inference(definition_unfolding,[],[f37,f39,f39])).
% 13.63/2.16  fof(f39,plain,(
% 13.63/2.16    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 13.63/2.16    inference(cnf_transformation,[],[f11])).
% 13.63/2.16  fof(f11,axiom,(
% 13.63/2.16    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 13.63/2.16  fof(f37,plain,(
% 13.63/2.16    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 13.63/2.16    inference(cnf_transformation,[],[f2])).
% 13.63/2.16  fof(f2,axiom,(
% 13.63/2.16    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 13.63/2.16  fof(f36,plain,(
% 13.63/2.16    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 13.63/2.16    inference(cnf_transformation,[],[f7])).
% 13.63/2.16  fof(f7,axiom,(
% 13.63/2.16    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 13.63/2.16  fof(f61,plain,(
% 13.63/2.16    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 13.63/2.16    inference(equality_resolution,[],[f50])).
% 13.63/2.16  fof(f50,plain,(
% 13.63/2.16    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 13.63/2.16    inference(cnf_transformation,[],[f3])).
% 13.63/2.16  fof(f3,axiom,(
% 13.63/2.16    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 13.63/2.16  fof(f23963,plain,(
% 13.63/2.16    ~spl4_10 | ~spl4_12 | ~spl4_199 | spl4_9 | ~spl4_138),
% 13.63/2.16    inference(avatar_split_clause,[],[f23958,f9272,f255,f23960,f585,f260])).
% 13.63/2.16  fof(f260,plain,(
% 13.63/2.16    spl4_10 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 13.63/2.16  fof(f585,plain,(
% 13.63/2.16    spl4_12 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 13.63/2.16  fof(f255,plain,(
% 13.63/2.16    spl4_9 <=> r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 13.63/2.16  fof(f9272,plain,(
% 13.63/2.16    spl4_138 <=> k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_138])])).
% 13.63/2.16  fof(f23958,plain,(
% 13.63/2.16    ~r1_tarski(sK1,k2_xboole_0(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | (spl4_9 | ~spl4_138)),
% 13.63/2.16    inference(superposition,[],[f23942,f59])).
% 13.63/2.16  fof(f59,plain,(
% 13.63/2.16    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 13.63/2.16    inference(cnf_transformation,[],[f30])).
% 13.63/2.16  fof(f30,plain,(
% 13.63/2.16    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 13.63/2.16    inference(flattening,[],[f29])).
% 13.63/2.16  fof(f29,plain,(
% 13.63/2.16    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 13.63/2.16    inference(ennf_transformation,[],[f18])).
% 13.63/2.16  fof(f18,axiom,(
% 13.63/2.16    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 13.63/2.16  fof(f23942,plain,(
% 13.63/2.16    ~r1_tarski(sK1,k4_subset_1(sK0,sK1,sK2)) | (spl4_9 | ~spl4_138)),
% 13.63/2.16    inference(resolution,[],[f23875,f659])).
% 13.63/2.16  fof(f659,plain,(
% 13.63/2.16    ( ! [X4,X5,X3] : (r1_tarski(k4_xboole_0(X5,X4),k4_xboole_0(X5,X3)) | ~r1_tarski(X3,X4)) )),
% 13.63/2.16    inference(superposition,[],[f346,f45])).
% 13.63/2.16  fof(f346,plain,(
% 13.63/2.16    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,k2_xboole_0(X1,X2)),k4_xboole_0(X0,X1))) )),
% 13.63/2.16    inference(superposition,[],[f36,f56])).
% 13.63/2.16  fof(f23875,plain,(
% 13.63/2.16    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k4_xboole_0(sK0,sK1)) | (spl4_9 | ~spl4_138)),
% 13.63/2.16    inference(forward_demodulation,[],[f257,f9274])).
% 13.63/2.16  fof(f9274,plain,(
% 13.63/2.16    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~spl4_138),
% 13.63/2.16    inference(avatar_component_clause,[],[f9272])).
% 13.63/2.16  fof(f257,plain,(
% 13.63/2.16    ~r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) | spl4_9),
% 13.63/2.16    inference(avatar_component_clause,[],[f255])).
% 13.63/2.16  fof(f23845,plain,(
% 13.63/2.16    ~spl4_2 | spl4_23 | ~spl4_41 | ~spl4_96),
% 13.63/2.16    inference(avatar_contradiction_clause,[],[f23805])).
% 13.63/2.16  fof(f23805,plain,(
% 13.63/2.16    $false | (~spl4_2 | spl4_23 | ~spl4_41 | ~spl4_96)),
% 13.63/2.16    inference(unit_resulting_resolution,[],[f88,f735,f10543])).
% 13.63/2.16  fof(f10543,plain,(
% 13.63/2.16    ( ! [X1] : (r1_tarski(k2_xboole_0(sK1,X1),sK0) | ~r1_tarski(X1,sK0)) ) | (~spl4_41 | ~spl4_96)),
% 13.63/2.16    inference(superposition,[],[f9810,f45])).
% 13.63/2.16  fof(f9810,plain,(
% 13.63/2.16    ( ! [X2] : (r1_tarski(k2_xboole_0(sK1,X2),k2_xboole_0(X2,sK0))) ) | (~spl4_41 | ~spl4_96)),
% 13.63/2.16    inference(superposition,[],[f8675,f38])).
% 13.63/2.16  fof(f8675,plain,(
% 13.63/2.16    ( ! [X0] : (r1_tarski(k2_xboole_0(X0,sK1),k2_xboole_0(X0,sK0))) ) | (~spl4_41 | ~spl4_96)),
% 13.63/2.16    inference(resolution,[],[f8415,f58])).
% 13.63/2.16  fof(f8415,plain,(
% 13.63/2.16    ( ! [X17] : (r1_tarski(k4_xboole_0(k2_xboole_0(X17,sK1),X17),sK0)) ) | (~spl4_41 | ~spl4_96)),
% 13.63/2.16    inference(resolution,[],[f8257,f7903])).
% 13.63/2.16  fof(f7903,plain,(
% 13.63/2.16    ( ! [X8] : (~r1_tarski(X8,sK1) | r1_tarski(X8,sK0)) ) | ~spl4_96),
% 13.63/2.16    inference(superposition,[],[f57,f7198])).
% 13.63/2.16  fof(f7198,plain,(
% 13.63/2.16    sK0 = k2_xboole_0(sK0,sK1) | ~spl4_96),
% 13.63/2.16    inference(avatar_component_clause,[],[f7196])).
% 13.63/2.16  fof(f7196,plain,(
% 13.63/2.16    spl4_96 <=> sK0 = k2_xboole_0(sK0,sK1)),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_96])])).
% 13.63/2.16  fof(f8257,plain,(
% 13.63/2.16    ( ! [X19,X18] : (r1_tarski(k4_xboole_0(k2_xboole_0(X18,X19),X18),X19)) ) | ~spl4_41),
% 13.63/2.16    inference(forward_demodulation,[],[f8200,f5536])).
% 13.63/2.16  fof(f5536,plain,(
% 13.63/2.16    ( ! [X4] : (k2_xboole_0(X4,k1_xboole_0) = X4) ) | ~spl4_41),
% 13.63/2.16    inference(superposition,[],[f5473,f3457])).
% 13.63/2.16  fof(f3457,plain,(
% 13.63/2.16    ( ! [X8] : (k2_xboole_0(X8,X8) = k2_xboole_0(X8,k1_xboole_0)) ) | ~spl4_41),
% 13.63/2.16    inference(superposition,[],[f40,f3427])).
% 13.63/2.16  fof(f3427,plain,(
% 13.63/2.16    ( ! [X10] : (k1_xboole_0 = k4_xboole_0(X10,X10)) ) | ~spl4_41),
% 13.63/2.16    inference(avatar_component_clause,[],[f3426])).
% 13.63/2.16  fof(f3426,plain,(
% 13.63/2.16    spl4_41 <=> ! [X10] : k1_xboole_0 = k4_xboole_0(X10,X10)),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 13.63/2.16  fof(f5473,plain,(
% 13.63/2.16    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 13.63/2.16    inference(resolution,[],[f110,f36])).
% 13.63/2.16  fof(f110,plain,(
% 13.63/2.16    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(X3,X2),X2) | k2_xboole_0(X2,X3) = X2) )),
% 13.63/2.16    inference(superposition,[],[f40,f92])).
% 13.63/2.16  fof(f8200,plain,(
% 13.63/2.16    ( ! [X19,X18] : (r1_tarski(k4_xboole_0(k2_xboole_0(X18,X19),k2_xboole_0(X18,k1_xboole_0)),X19)) ) | ~spl4_41),
% 13.63/2.16    inference(superposition,[],[f436,f3427])).
% 13.63/2.16  fof(f436,plain,(
% 13.63/2.16    ( ! [X8,X7,X9] : (r1_tarski(k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,k2_xboole_0(X8,X9)))),X9)) )),
% 13.63/2.16    inference(forward_demodulation,[],[f427,f56])).
% 13.63/2.16  fof(f427,plain,(
% 13.63/2.16    ( ! [X8,X7,X9] : (r1_tarski(k4_xboole_0(k4_xboole_0(X7,X8),k4_xboole_0(X7,k2_xboole_0(X8,X9))),X9)) )),
% 13.63/2.16    inference(superposition,[],[f389,f56])).
% 13.63/2.16  fof(f389,plain,(
% 13.63/2.16    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) )),
% 13.63/2.16    inference(superposition,[],[f36,f60])).
% 13.63/2.16  fof(f735,plain,(
% 13.63/2.16    ~r1_tarski(k2_xboole_0(sK1,sK2),sK0) | spl4_23),
% 13.63/2.16    inference(avatar_component_clause,[],[f733])).
% 13.63/2.16  fof(f733,plain,(
% 13.63/2.16    spl4_23 <=> r1_tarski(k2_xboole_0(sK1,sK2),sK0)),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 13.63/2.16  fof(f88,plain,(
% 13.63/2.16    r1_tarski(sK2,sK0) | ~spl4_2),
% 13.63/2.16    inference(resolution,[],[f81,f63])).
% 13.63/2.16  fof(f63,plain,(
% 13.63/2.16    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 13.63/2.16    inference(equality_resolution,[],[f53])).
% 13.63/2.16  fof(f53,plain,(
% 13.63/2.16    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 13.63/2.16    inference(cnf_transformation,[],[f12])).
% 13.63/2.16  fof(f12,axiom,(
% 13.63/2.16    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 13.63/2.16  fof(f81,plain,(
% 13.63/2.16    r2_hidden(sK2,k1_zfmisc_1(sK0)) | ~spl4_2),
% 13.63/2.16    inference(avatar_component_clause,[],[f79])).
% 13.63/2.16  fof(f79,plain,(
% 13.63/2.16    spl4_2 <=> r2_hidden(sK2,k1_zfmisc_1(sK0))),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 13.63/2.16  fof(f9455,plain,(
% 13.63/2.16    spl4_137),
% 13.63/2.16    inference(avatar_contradiction_clause,[],[f9447])).
% 13.63/2.16  fof(f9447,plain,(
% 13.63/2.16    $false | spl4_137),
% 13.63/2.16    inference(unit_resulting_resolution,[],[f34,f36,f9270,f70])).
% 13.63/2.16  fof(f70,plain,(
% 13.63/2.16    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(k1_zfmisc_1(X0)) | ~r1_tarski(X1,X0)) )),
% 13.63/2.16    inference(resolution,[],[f43,f64])).
% 13.63/2.16  fof(f64,plain,(
% 13.63/2.16    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 13.63/2.16    inference(equality_resolution,[],[f52])).
% 13.63/2.16  fof(f52,plain,(
% 13.63/2.16    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 13.63/2.16    inference(cnf_transformation,[],[f12])).
% 13.63/2.16  fof(f43,plain,(
% 13.63/2.16    ( ! [X0,X1] : (~r2_hidden(X1,X0) | v1_xboole_0(X0) | m1_subset_1(X1,X0)) )),
% 13.63/2.16    inference(cnf_transformation,[],[f22])).
% 13.63/2.16  fof(f22,plain,(
% 13.63/2.16    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 13.63/2.16    inference(ennf_transformation,[],[f13])).
% 13.63/2.16  fof(f13,axiom,(
% 13.63/2.16    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 13.63/2.16  fof(f9270,plain,(
% 13.63/2.16    ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | spl4_137),
% 13.63/2.16    inference(avatar_component_clause,[],[f9268])).
% 13.63/2.16  fof(f9268,plain,(
% 13.63/2.16    spl4_137 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_137])])).
% 13.63/2.16  fof(f34,plain,(
% 13.63/2.16    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 13.63/2.16    inference(cnf_transformation,[],[f16])).
% 13.63/2.16  fof(f16,axiom,(
% 13.63/2.16    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).
% 13.63/2.16  fof(f9275,plain,(
% 13.63/2.16    ~spl4_137 | spl4_138 | ~spl4_41 | ~spl4_96),
% 13.63/2.16    inference(avatar_split_clause,[],[f9225,f7196,f3426,f9272,f9268])).
% 13.63/2.16  fof(f9225,plain,(
% 13.63/2.16    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) | ~m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | (~spl4_41 | ~spl4_96)),
% 13.63/2.16    inference(superposition,[],[f290,f8050])).
% 13.63/2.16  fof(f8050,plain,(
% 13.63/2.16    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl4_41 | ~spl4_96)),
% 13.63/2.16    inference(forward_demodulation,[],[f8006,f5904])).
% 13.63/2.16  fof(f5904,plain,(
% 13.63/2.16    ( ! [X7] : (k4_xboole_0(X7,k1_xboole_0) = X7) ) | ~spl4_41),
% 13.63/2.16    inference(forward_demodulation,[],[f5794,f5535])).
% 13.63/2.16  fof(f5535,plain,(
% 13.63/2.16    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = X3) ) | ~spl4_41),
% 13.63/2.16    inference(superposition,[],[f5473,f3525])).
% 13.63/2.16  fof(f3525,plain,(
% 13.63/2.16    ( ! [X3] : (k2_xboole_0(X3,X3) = k2_xboole_0(k1_xboole_0,X3)) ) | ~spl4_41),
% 13.63/2.16    inference(superposition,[],[f3457,f38])).
% 13.63/2.16  fof(f5794,plain,(
% 13.63/2.16    ( ! [X7] : (k4_xboole_0(X7,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X7)) ) | ~spl4_41),
% 13.63/2.16    inference(superposition,[],[f5535,f40])).
% 13.63/2.16  fof(f8006,plain,(
% 13.63/2.16    k4_xboole_0(sK1,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl4_41 | ~spl4_96)),
% 13.63/2.16    inference(superposition,[],[f60,f7948])).
% 13.63/2.16  fof(f7948,plain,(
% 13.63/2.16    k1_xboole_0 = k4_xboole_0(sK1,sK0) | (~spl4_41 | ~spl4_96)),
% 13.63/2.16    inference(superposition,[],[f3512,f7198])).
% 13.63/2.16  fof(f3512,plain,(
% 13.63/2.16    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,X7))) ) | ~spl4_41),
% 13.63/2.16    inference(forward_demodulation,[],[f3451,f40])).
% 13.63/2.16  fof(f3451,plain,(
% 13.63/2.16    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8)))) ) | ~spl4_41),
% 13.63/2.16    inference(superposition,[],[f3427,f56])).
% 13.63/2.16  fof(f290,plain,(
% 13.63/2.16    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 13.63/2.16    inference(duplicate_literal_removal,[],[f286])).
% 13.63/2.16  fof(f286,plain,(
% 13.63/2.16    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 13.63/2.16    inference(superposition,[],[f48,f47])).
% 13.63/2.16  fof(f47,plain,(
% 13.63/2.16    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 13.63/2.16    inference(cnf_transformation,[],[f25])).
% 13.63/2.16  fof(f25,plain,(
% 13.63/2.16    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 13.63/2.16    inference(ennf_transformation,[],[f14])).
% 13.63/2.16  fof(f14,axiom,(
% 13.63/2.16    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 13.63/2.16  fof(f48,plain,(
% 13.63/2.16    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 13.63/2.16    inference(cnf_transformation,[],[f26])).
% 13.63/2.16  fof(f26,plain,(
% 13.63/2.16    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 13.63/2.16    inference(ennf_transformation,[],[f17])).
% 13.63/2.16  fof(f17,axiom,(
% 13.63/2.16    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 13.63/2.16  fof(f7884,plain,(
% 13.63/2.16    spl4_96 | ~spl4_63 | ~spl4_85),
% 13.63/2.16    inference(avatar_split_clause,[],[f7881,f7074,f6781,f7196])).
% 13.63/2.16  fof(f6781,plain,(
% 13.63/2.16    spl4_63 <=> r1_tarski(sK0,k2_xboole_0(sK0,sK1))),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 13.63/2.16  fof(f7074,plain,(
% 13.63/2.16    spl4_85 <=> r1_tarski(k2_xboole_0(sK0,sK1),sK0)),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 13.63/2.16  fof(f7881,plain,(
% 13.63/2.16    ~r1_tarski(sK0,k2_xboole_0(sK0,sK1)) | sK0 = k2_xboole_0(sK0,sK1) | ~spl4_85),
% 13.63/2.16    inference(resolution,[],[f7076,f51])).
% 13.63/2.16  fof(f51,plain,(
% 13.63/2.16    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 13.63/2.16    inference(cnf_transformation,[],[f3])).
% 13.63/2.16  fof(f7076,plain,(
% 13.63/2.16    r1_tarski(k2_xboole_0(sK0,sK1),sK0) | ~spl4_85),
% 13.63/2.16    inference(avatar_component_clause,[],[f7074])).
% 13.63/2.16  fof(f7873,plain,(
% 13.63/2.16    spl4_125),
% 13.63/2.16    inference(avatar_contradiction_clause,[],[f7868])).
% 13.63/2.16  fof(f7868,plain,(
% 13.63/2.16    $false | spl4_125),
% 13.63/2.16    inference(unit_resulting_resolution,[],[f61,f61,f7865,f102])).
% 13.63/2.16  fof(f102,plain,(
% 13.63/2.16    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | r1_tarski(X2,X0) | ~r1_tarski(X1,X0)) )),
% 13.63/2.16    inference(superposition,[],[f57,f92])).
% 13.63/2.16  fof(f7865,plain,(
% 13.63/2.16    ~r1_tarski(sK0,sK0) | spl4_125),
% 13.63/2.16    inference(avatar_component_clause,[],[f7863])).
% 13.63/2.16  fof(f7863,plain,(
% 13.63/2.16    spl4_125 <=> r1_tarski(sK0,sK0)),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_125])])).
% 13.63/2.16  fof(f7866,plain,(
% 13.63/2.16    ~spl4_84 | ~spl4_125 | spl4_85),
% 13.63/2.16    inference(avatar_split_clause,[],[f7860,f7074,f7863,f7070])).
% 13.63/2.16  fof(f7070,plain,(
% 13.63/2.16    spl4_84 <=> r1_tarski(sK1,sK0)),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).
% 13.63/2.16  fof(f7860,plain,(
% 13.63/2.16    ~r1_tarski(sK0,sK0) | ~r1_tarski(sK1,sK0) | spl4_85),
% 13.63/2.16    inference(superposition,[],[f7075,f92])).
% 13.63/2.16  fof(f7075,plain,(
% 13.63/2.16    ~r1_tarski(k2_xboole_0(sK0,sK1),sK0) | spl4_85),
% 13.63/2.16    inference(avatar_component_clause,[],[f7074])).
% 13.63/2.16  fof(f7089,plain,(
% 13.63/2.16    ~spl4_3 | spl4_84),
% 13.63/2.16    inference(avatar_contradiction_clause,[],[f7082])).
% 13.63/2.16  fof(f7082,plain,(
% 13.63/2.16    $false | (~spl4_3 | spl4_84)),
% 13.63/2.16    inference(subsumption_resolution,[],[f2102,f7072])).
% 13.63/2.16  fof(f7072,plain,(
% 13.63/2.16    ~r1_tarski(sK1,sK0) | spl4_84),
% 13.63/2.16    inference(avatar_component_clause,[],[f7070])).
% 13.63/2.16  fof(f2102,plain,(
% 13.63/2.16    r1_tarski(sK1,sK0) | ~spl4_3),
% 13.63/2.16    inference(resolution,[],[f86,f63])).
% 13.63/2.16  fof(f86,plain,(
% 13.63/2.16    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl4_3),
% 13.63/2.16    inference(avatar_component_clause,[],[f84])).
% 13.63/2.16  fof(f84,plain,(
% 13.63/2.16    spl4_3 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 13.63/2.16  fof(f6931,plain,(
% 13.63/2.16    ~spl4_10 | ~spl4_12 | spl4_51 | ~spl4_9),
% 13.63/2.16    inference(avatar_split_clause,[],[f6916,f255,f6675,f585,f260])).
% 13.63/2.16  fof(f6675,plain,(
% 13.63/2.16    spl4_51 <=> r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_51])])).
% 13.63/2.16  fof(f6916,plain,(
% 13.63/2.16    r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl4_9),
% 13.63/2.16    inference(superposition,[],[f256,f59])).
% 13.63/2.16  fof(f256,plain,(
% 13.63/2.16    r1_tarski(k4_xboole_0(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1)) | ~spl4_9),
% 13.63/2.16    inference(avatar_component_clause,[],[f255])).
% 13.63/2.16  fof(f6801,plain,(
% 13.63/2.16    spl4_63),
% 13.63/2.16    inference(avatar_contradiction_clause,[],[f6789])).
% 13.63/2.16  fof(f6789,plain,(
% 13.63/2.16    $false | spl4_63),
% 13.63/2.16    inference(unit_resulting_resolution,[],[f214,f61,f6783,f102])).
% 13.63/2.16  fof(f6783,plain,(
% 13.63/2.16    ~r1_tarski(sK0,k2_xboole_0(sK0,sK1)) | spl4_63),
% 13.63/2.16    inference(avatar_component_clause,[],[f6781])).
% 13.63/2.16  fof(f214,plain,(
% 13.63/2.16    ( ! [X4,X5] : (r1_tarski(X5,k2_xboole_0(X5,X4))) )),
% 13.63/2.16    inference(superposition,[],[f199,f38])).
% 13.63/2.16  fof(f199,plain,(
% 13.63/2.16    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 13.63/2.16    inference(resolution,[],[f58,f36])).
% 13.63/2.16  fof(f6678,plain,(
% 13.63/2.16    ~spl4_13 | ~spl4_51 | spl4_14),
% 13.63/2.16    inference(avatar_split_clause,[],[f627,f594,f6675,f589])).
% 13.63/2.16  fof(f589,plain,(
% 13.63/2.16    spl4_13 <=> m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0))),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 13.63/2.16  fof(f594,plain,(
% 13.63/2.16    spl4_14 <=> r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1))),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 13.63/2.16  fof(f627,plain,(
% 13.63/2.16    ~r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) | ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl4_14),
% 13.63/2.16    inference(superposition,[],[f596,f47])).
% 13.63/2.16  fof(f596,plain,(
% 13.63/2.16    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) | spl4_14),
% 13.63/2.16    inference(avatar_component_clause,[],[f594])).
% 13.63/2.16  fof(f3447,plain,(
% 13.63/2.16    spl4_42),
% 13.63/2.16    inference(avatar_contradiction_clause,[],[f3439])).
% 13.63/2.16  fof(f3439,plain,(
% 13.63/2.16    $false | spl4_42),
% 13.63/2.16    inference(unit_resulting_resolution,[],[f35,f61,f3431,f102])).
% 13.63/2.16  fof(f3431,plain,(
% 13.63/2.16    ~r1_tarski(k1_xboole_0,k1_xboole_0) | spl4_42),
% 13.63/2.16    inference(avatar_component_clause,[],[f3429])).
% 13.63/2.16  fof(f3429,plain,(
% 13.63/2.16    spl4_42 <=> r1_tarski(k1_xboole_0,k1_xboole_0)),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 13.63/2.16  fof(f35,plain,(
% 13.63/2.16    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 13.63/2.16    inference(cnf_transformation,[],[f6])).
% 13.63/2.16  fof(f6,axiom,(
% 13.63/2.16    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 13.63/2.16  fof(f3432,plain,(
% 13.63/2.16    spl4_41 | ~spl4_42),
% 13.63/2.16    inference(avatar_split_clause,[],[f3415,f3429,f3426])).
% 13.63/2.16  fof(f3415,plain,(
% 13.63/2.16    ( ! [X10] : (~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(X10,X10)) )),
% 13.63/2.16    inference(resolution,[],[f3127,f116])).
% 13.63/2.16  fof(f116,plain,(
% 13.63/2.16    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 13.63/2.16    inference(resolution,[],[f51,f35])).
% 13.63/2.16  fof(f3127,plain,(
% 13.63/2.16    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X1,X1),X0) | ~r1_tarski(X0,X0)) )),
% 13.63/2.16    inference(superposition,[],[f3092,f92])).
% 13.63/2.16  fof(f3092,plain,(
% 13.63/2.16    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X2),k2_xboole_0(X3,X3))) )),
% 13.63/2.16    inference(resolution,[],[f3067,f348])).
% 13.63/2.16  fof(f348,plain,(
% 13.63/2.16    ( ! [X6,X8,X7,X9] : (~r1_tarski(k4_xboole_0(X6,k2_xboole_0(X7,X8)),X9) | r1_tarski(k4_xboole_0(X6,X7),k2_xboole_0(X8,X9))) )),
% 13.63/2.16    inference(superposition,[],[f58,f56])).
% 13.63/2.16  fof(f2101,plain,(
% 13.63/2.16    ~spl4_1),
% 13.63/2.16    inference(avatar_contradiction_clause,[],[f2098])).
% 13.63/2.16  fof(f2098,plain,(
% 13.63/2.16    $false | ~spl4_1),
% 13.63/2.16    inference(unit_resulting_resolution,[],[f34,f77])).
% 13.63/2.16  fof(f77,plain,(
% 13.63/2.16    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl4_1),
% 13.63/2.16    inference(avatar_component_clause,[],[f75])).
% 13.63/2.16  fof(f75,plain,(
% 13.63/2.16    spl4_1 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 13.63/2.16    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 13.63/2.16  fof(f2097,plain,(
% 13.63/2.16    spl4_1 | spl4_3),
% 13.63/2.16    inference(avatar_split_clause,[],[f603,f84,f75])).
% 13.63/2.16  fof(f603,plain,(
% 13.63/2.16    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 13.63/2.16    inference(resolution,[],[f33,f44])).
% 13.63/2.16  fof(f44,plain,(
% 13.63/2.16    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 13.63/2.16    inference(cnf_transformation,[],[f22])).
% 13.63/2.16  fof(f33,plain,(
% 13.63/2.16    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 13.63/2.16    inference(cnf_transformation,[],[f21])).
% 13.63/2.16  fof(f21,plain,(
% 13.63/2.16    ? [X0,X1] : (? [X2] : (~r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 13.63/2.16    inference(ennf_transformation,[],[f20])).
% 13.63/2.16  fof(f20,negated_conjecture,(
% 13.63/2.16    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 13.63/2.16    inference(negated_conjecture,[],[f19])).
% 13.63/2.16  fof(f19,conjecture,(
% 13.63/2.16    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 13.63/2.16    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 13.63/2.16  fof(f736,plain,(
% 13.63/2.16    ~spl4_23 | spl4_1 | spl4_13),
% 13.63/2.16    inference(avatar_split_clause,[],[f725,f589,f75,f733])).
% 13.63/2.16  fof(f725,plain,(
% 13.63/2.16    v1_xboole_0(k1_zfmisc_1(sK0)) | ~r1_tarski(k2_xboole_0(sK1,sK2),sK0) | spl4_13),
% 13.63/2.16    inference(resolution,[],[f70,f591])).
% 13.63/2.16  fof(f591,plain,(
% 13.63/2.16    ~m1_subset_1(k2_xboole_0(sK1,sK2),k1_zfmisc_1(sK0)) | spl4_13),
% 13.63/2.16    inference(avatar_component_clause,[],[f589])).
% 13.63/2.16  fof(f609,plain,(
% 13.63/2.16    spl4_12),
% 13.63/2.16    inference(avatar_contradiction_clause,[],[f605])).
% 13.63/2.16  fof(f605,plain,(
% 13.63/2.16    $false | spl4_12),
% 13.63/2.16    inference(subsumption_resolution,[],[f31,f587])).
% 13.63/2.16  fof(f587,plain,(
% 13.63/2.16    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl4_12),
% 13.63/2.16    inference(avatar_component_clause,[],[f585])).
% 13.63/2.16  fof(f31,plain,(
% 13.63/2.16    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 13.63/2.16    inference(cnf_transformation,[],[f21])).
% 13.63/2.16  fof(f602,plain,(
% 13.63/2.16    spl4_10),
% 13.63/2.16    inference(avatar_contradiction_clause,[],[f598])).
% 13.63/2.16  fof(f598,plain,(
% 13.63/2.16    $false | spl4_10),
% 13.63/2.16    inference(subsumption_resolution,[],[f33,f262])).
% 13.63/2.16  fof(f262,plain,(
% 13.63/2.16    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl4_10),
% 13.63/2.16    inference(avatar_component_clause,[],[f260])).
% 13.63/2.16  fof(f597,plain,(
% 13.63/2.16    ~spl4_10 | ~spl4_12 | ~spl4_14),
% 13.63/2.16    inference(avatar_split_clause,[],[f583,f594,f585,f260])).
% 13.63/2.16  fof(f583,plain,(
% 13.63/2.16    ~r1_tarski(k3_subset_1(sK0,k2_xboole_0(sK1,sK2)),k3_subset_1(sK0,sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 13.63/2.16    inference(superposition,[],[f32,f59])).
% 13.63/2.16  fof(f32,plain,(
% 13.63/2.16    ~r1_tarski(k3_subset_1(sK0,k4_subset_1(sK0,sK1,sK2)),k3_subset_1(sK0,sK1))),
% 13.63/2.16    inference(cnf_transformation,[],[f21])).
% 13.63/2.16  fof(f82,plain,(
% 13.63/2.16    spl4_1 | spl4_2),
% 13.63/2.16    inference(avatar_split_clause,[],[f71,f79,f75])).
% 13.63/2.16  fof(f71,plain,(
% 13.63/2.16    r2_hidden(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0))),
% 13.63/2.16    inference(resolution,[],[f44,f31])).
% 13.63/2.16  % SZS output end Proof for theBenchmark
% 13.63/2.16  % (13030)------------------------------
% 13.63/2.16  % (13030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 13.63/2.16  % (13030)Termination reason: Refutation
% 13.63/2.16  
% 13.63/2.16  % (13030)Memory used [KB]: 23539
% 13.63/2.16  % (13030)Time elapsed: 1.735 s
% 13.63/2.16  % (13030)------------------------------
% 13.63/2.16  % (13030)------------------------------
% 13.63/2.16  % (13016)Success in time 1.794 s
%------------------------------------------------------------------------------
