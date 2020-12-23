%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 464 expanded)
%              Number of leaves         :   30 ( 155 expanded)
%              Depth                    :   17
%              Number of atoms          :  284 ( 764 expanded)
%              Number of equality atoms :   96 ( 400 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f91,f100,f136,f236,f241,f326,f614,f1304,f1355])).

fof(f1355,plain,
    ( spl2_3
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_19
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f1354])).

fof(f1354,plain,
    ( $false
    | spl2_3
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_19
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f1353,f613])).

fof(f613,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f611])).

fof(f611,plain,
    ( spl2_19
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f1353,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl2_3
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f1352,f1338])).

fof(f1338,plain,
    ( sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ spl2_8
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f1337,f158])).

fof(f158,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f157,f66])).

fof(f66,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f40,f63])).

fof(f63,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f43,f39])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f43,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f40,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f157,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f152,f122])).

fof(f122,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f103,f46])).

% (3162)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% (3171)Refutation not found, incomplete strategy% (3171)------------------------------
% (3171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3171)Termination reason: Refutation not found, incomplete strategy

% (3171)Memory used [KB]: 10746
% (3171)Time elapsed: 0.161 s
% (3171)------------------------------
% (3171)------------------------------
fof(f46,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f103,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f38,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f38,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f152,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f41,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f51])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f1337,plain,
    ( k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_8
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f1335,f160])).

fof(f160,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f159,f133])).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f130,f66])).

fof(f130,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f41,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f159,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f151,f104])).

fof(f104,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f73,f52])).

fof(f73,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f151,plain,(
    ! [X0] : k3_subset_1(X0,X0) = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f77,f72])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f67,f66])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f42,f63])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f1335,plain,
    ( k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))
    | ~ spl2_8
    | ~ spl2_26 ),
    inference(backward_demodulation,[],[f1081,f1313])).

fof(f1313,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_26 ),
    inference(superposition,[],[f1303,f46])).

fof(f1303,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f1301])).

fof(f1301,plain,
    ( spl2_26
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f1081,plain,
    ( k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f1045,f46])).

fof(f1045,plain,
    ( k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl2_8 ),
    inference(superposition,[],[f416,f240])).

fof(f240,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f238])).

fof(f238,plain,
    ( spl2_8
  <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f416,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))) = k5_xboole_0(X7,k5_xboole_0(X6,k3_xboole_0(X6,X7))) ),
    inference(superposition,[],[f165,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f50,f62,f51])).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f48,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f165,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X1,X1,X1,X0)) ),
    inference(superposition,[],[f71,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f45,f61,f61])).

fof(f45,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1352,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK1,k3_subset_1(sK0,sK1)))
    | spl2_3
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f1341,f89])).

fof(f89,plain,
    ( sK0 != sK1
    | spl2_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1341,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,k5_xboole_0(sK1,k3_subset_1(sK0,sK1)))
    | ~ spl2_8
    | ~ spl2_11
    | ~ spl2_26 ),
    inference(backward_demodulation,[],[f405,f1338])).

fof(f405,plain,
    ( sK1 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1))
    | ~ r1_tarski(sK1,k5_xboole_0(sK1,k3_subset_1(sK0,sK1)))
    | ~ spl2_11 ),
    inference(resolution,[],[f325,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f325,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl2_11
  <=> r1_tarski(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f1304,plain,
    ( spl2_26
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f711,f611,f1301])).

fof(f711,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_19 ),
    inference(unit_resulting_resolution,[],[f613,f52])).

fof(f614,plain,
    ( spl2_19
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f601,f79,f611])).

fof(f79,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f601,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f81,f230])).

fof(f230,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | r1_tarski(X3,X2) ) ),
    inference(subsumption_resolution,[],[f229,f77])).

fof(f229,plain,(
    ! [X2,X3] :
      ( r1_tarski(X3,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f225,f38])).

fof(f225,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k1_xboole_0,k3_subset_1(X2,X3))
      | r1_tarski(X3,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f56,f133])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f81,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f326,plain,
    ( spl2_11
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f296,f233,f323])).

fof(f233,plain,
    ( spl2_7
  <=> k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f296,plain,
    ( r1_tarski(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),sK1)
    | ~ spl2_7 ),
    inference(superposition,[],[f101,f235])).

fof(f235,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f233])).

fof(f101,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0) ),
    inference(superposition,[],[f68,f46])).

fof(f68,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f44,f51])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f241,plain,
    ( spl2_8
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f153,f79,f238])).

fof(f153,plain,
    ( k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f81,f72])).

fof(f236,plain,
    ( spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f143,f84,f233])).

fof(f84,plain,
    ( spl2_2
  <=> r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f143,plain,
    ( k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f86,f52])).

fof(f86,plain,
    ( r1_tarski(k3_subset_1(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f136,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f134,f38])).

fof(f134,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl2_4 ),
    inference(backward_demodulation,[],[f99,f133])).

fof(f99,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | spl2_4 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl2_4
  <=> r1_tarski(k3_subset_1(sK0,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f100,plain,
    ( ~ spl2_4
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f94,f88,f97])).

fof(f94,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f93,f90])).

fof(f90,plain,
    ( sK0 = sK1
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f93,plain,
    ( ~ r1_tarski(k3_subset_1(sK0,sK0),sK0)
    | sK0 != sK1
    | ~ spl2_3 ),
    inference(backward_demodulation,[],[f76,f90])).

fof(f76,plain,
    ( sK0 != sK1
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f64,f66])).

fof(f64,plain,
    ( sK1 != k3_subset_1(sK0,k1_xboole_0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f37,f63])).

fof(f37,plain,
    ( sK1 != k2_subset_1(sK0)
    | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( sK1 != k2_subset_1(sK0)
      | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & ( sK1 = k2_subset_1(sK0)
      | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( k2_subset_1(X0) != X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
        & ( k2_subset_1(X0) = X1
          | r1_tarski(k3_subset_1(X0,X1),X1) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ( sK1 != k2_subset_1(sK0)
        | ~ r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & ( sK1 = k2_subset_1(sK0)
        | r1_tarski(k3_subset_1(sK0,sK1),sK1) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( k2_subset_1(X0) != X1
        | ~ r1_tarski(k3_subset_1(X0,X1),X1) )
      & ( k2_subset_1(X0) = X1
        | r1_tarski(k3_subset_1(X0,X1),X1) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <~> k2_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(k3_subset_1(X0,X1),X1)
        <=> k2_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

fof(f91,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f75,f88,f84])).

fof(f75,plain,
    ( sK0 = sK1
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f65,f66])).

fof(f65,plain,
    ( sK1 = k3_subset_1(sK0,k1_xboole_0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(definition_unfolding,[],[f36,f63])).

fof(f36,plain,
    ( sK1 = k2_subset_1(sK0)
    | r1_tarski(k3_subset_1(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f35,f79])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:40:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (3146)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (3154)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.51  % (3145)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (3147)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (3169)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (3163)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.52  % (3148)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (3153)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (3170)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.53  % (3152)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.53  % (3161)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.53  % (3155)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.53  % (3155)Refutation not found, incomplete strategy% (3155)------------------------------
% 0.22/0.53  % (3155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3160)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (3153)Refutation not found, incomplete strategy% (3153)------------------------------
% 0.22/0.54  % (3153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3167)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (3155)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (3155)Memory used [KB]: 10746
% 0.22/0.54  % (3155)Time elapsed: 0.122 s
% 0.22/0.54  % (3155)------------------------------
% 0.22/0.54  % (3155)------------------------------
% 0.22/0.54  % (3169)Refutation not found, incomplete strategy% (3169)------------------------------
% 0.22/0.54  % (3169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (3159)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.54  % (3159)Refutation not found, incomplete strategy% (3159)------------------------------
% 0.22/0.54  % (3159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (3164)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (3159)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (3159)Memory used [KB]: 10618
% 0.22/0.55  % (3153)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  % (3159)Time elapsed: 0.130 s
% 0.22/0.55  % (3159)------------------------------
% 0.22/0.55  % (3159)------------------------------
% 0.22/0.55  
% 0.22/0.55  % (3153)Memory used [KB]: 10746
% 0.22/0.55  % (3153)Time elapsed: 0.126 s
% 0.22/0.55  % (3153)------------------------------
% 0.22/0.55  % (3153)------------------------------
% 0.22/0.55  % (3161)Refutation not found, incomplete strategy% (3161)------------------------------
% 0.22/0.55  % (3161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (3169)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (3169)Memory used [KB]: 6396
% 0.22/0.55  % (3169)Time elapsed: 0.126 s
% 0.22/0.55  % (3169)------------------------------
% 0.22/0.55  % (3169)------------------------------
% 0.22/0.55  % (3143)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.55  % (3161)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (3161)Memory used [KB]: 1791
% 0.22/0.55  % (3161)Time elapsed: 0.126 s
% 0.22/0.55  % (3161)------------------------------
% 0.22/0.55  % (3161)------------------------------
% 0.22/0.56  % (3144)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.56  % (3144)Refutation not found, incomplete strategy% (3144)------------------------------
% 0.22/0.56  % (3144)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (3144)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (3144)Memory used [KB]: 1663
% 0.22/0.56  % (3144)Time elapsed: 0.147 s
% 0.22/0.56  % (3144)------------------------------
% 0.22/0.56  % (3144)------------------------------
% 0.22/0.56  % (3165)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (3172)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.57  % (3172)Refutation not found, incomplete strategy% (3172)------------------------------
% 0.22/0.57  % (3172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (3172)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (3172)Memory used [KB]: 1663
% 0.22/0.57  % (3172)Time elapsed: 0.127 s
% 0.22/0.57  % (3172)------------------------------
% 0.22/0.57  % (3172)------------------------------
% 0.22/0.57  % (3157)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.57  % (3166)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.57  % (3158)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (3171)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.57  % (3156)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.57  % (3151)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.58  % (3150)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.58  % (3163)Refutation found. Thanks to Tanya!
% 0.22/0.58  % SZS status Theorem for theBenchmark
% 0.22/0.58  % (3168)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.58  % (3149)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.59  % (3157)Refutation not found, incomplete strategy% (3157)------------------------------
% 0.22/0.59  % (3157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (3157)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (3157)Memory used [KB]: 1791
% 0.22/0.59  % (3157)Time elapsed: 0.163 s
% 0.22/0.59  % (3157)------------------------------
% 0.22/0.59  % (3157)------------------------------
% 0.22/0.59  % SZS output start Proof for theBenchmark
% 0.22/0.59  fof(f1419,plain,(
% 0.22/0.59    $false),
% 0.22/0.59    inference(avatar_sat_refutation,[],[f82,f91,f100,f136,f236,f241,f326,f614,f1304,f1355])).
% 0.22/0.59  fof(f1355,plain,(
% 0.22/0.59    spl2_3 | ~spl2_8 | ~spl2_11 | ~spl2_19 | ~spl2_26),
% 0.22/0.59    inference(avatar_contradiction_clause,[],[f1354])).
% 0.22/0.59  fof(f1354,plain,(
% 0.22/0.59    $false | (spl2_3 | ~spl2_8 | ~spl2_11 | ~spl2_19 | ~spl2_26)),
% 0.22/0.59    inference(subsumption_resolution,[],[f1353,f613])).
% 0.22/0.59  fof(f613,plain,(
% 0.22/0.59    r1_tarski(sK1,sK0) | ~spl2_19),
% 0.22/0.59    inference(avatar_component_clause,[],[f611])).
% 0.22/0.59  fof(f611,plain,(
% 0.22/0.59    spl2_19 <=> r1_tarski(sK1,sK0)),
% 0.22/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.59  fof(f1353,plain,(
% 0.22/0.59    ~r1_tarski(sK1,sK0) | (spl2_3 | ~spl2_8 | ~spl2_11 | ~spl2_26)),
% 0.22/0.59    inference(forward_demodulation,[],[f1352,f1338])).
% 0.22/0.59  fof(f1338,plain,(
% 0.22/0.59    sK0 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) | (~spl2_8 | ~spl2_26)),
% 0.22/0.59    inference(forward_demodulation,[],[f1337,f158])).
% 0.22/0.59  fof(f158,plain,(
% 0.22/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.59    inference(forward_demodulation,[],[f157,f66])).
% 0.22/0.59  fof(f66,plain,(
% 0.22/0.59    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.22/0.59    inference(definition_unfolding,[],[f40,f63])).
% 0.22/0.59  fof(f63,plain,(
% 0.22/0.59    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.22/0.59    inference(definition_unfolding,[],[f43,f39])).
% 0.22/0.59  fof(f39,plain,(
% 0.22/0.59    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.22/0.59    inference(cnf_transformation,[],[f13])).
% 0.22/0.59  fof(f13,axiom,(
% 0.22/0.59    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.22/0.59  fof(f43,plain,(
% 0.22/0.59    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.22/0.59    inference(cnf_transformation,[],[f18])).
% 0.22/0.59  fof(f18,axiom,(
% 0.22/0.59    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.22/0.59  fof(f40,plain,(
% 0.22/0.59    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.22/0.59    inference(cnf_transformation,[],[f14])).
% 0.22/0.59  fof(f14,axiom,(
% 0.22/0.59    ! [X0] : k2_subset_1(X0) = X0),
% 0.22/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.22/0.59  fof(f157,plain,(
% 0.22/0.59    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.59    inference(forward_demodulation,[],[f152,f122])).
% 0.22/0.59  fof(f122,plain,(
% 0.22/0.59    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.22/0.59    inference(superposition,[],[f103,f46])).
% 0.22/0.59  % (3162)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.59  % (3171)Refutation not found, incomplete strategy% (3171)------------------------------
% 0.22/0.59  % (3171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (3171)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (3171)Memory used [KB]: 10746
% 0.22/0.59  % (3171)Time elapsed: 0.161 s
% 0.22/0.59  % (3171)------------------------------
% 0.22/0.59  % (3171)------------------------------
% 1.69/0.59  fof(f46,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f1])).
% 1.69/0.59  fof(f1,axiom,(
% 1.69/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.69/0.59  fof(f103,plain,(
% 1.69/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f38,f52])).
% 1.69/0.59  fof(f52,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.69/0.59    inference(cnf_transformation,[],[f24])).
% 1.69/0.59  fof(f24,plain,(
% 1.69/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.69/0.59    inference(ennf_transformation,[],[f5])).
% 1.69/0.59  fof(f5,axiom,(
% 1.69/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.69/0.59  fof(f38,plain,(
% 1.69/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.69/0.59    inference(cnf_transformation,[],[f6])).
% 1.69/0.59  fof(f6,axiom,(
% 1.69/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.69/0.59  fof(f152,plain,(
% 1.69/0.59    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f41,f72])).
% 1.69/0.59  fof(f72,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)) )),
% 1.69/0.59    inference(definition_unfolding,[],[f53,f51])).
% 1.69/0.59  fof(f51,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f3])).
% 1.69/0.59  fof(f3,axiom,(
% 1.69/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.69/0.59  fof(f53,plain,(
% 1.69/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f25])).
% 1.69/0.59  fof(f25,plain,(
% 1.69/0.59    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.69/0.59    inference(ennf_transformation,[],[f15])).
% 1.69/0.59  fof(f15,axiom,(
% 1.69/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.69/0.59  fof(f41,plain,(
% 1.69/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f20])).
% 1.69/0.59  fof(f20,axiom,(
% 1.69/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.69/0.59  fof(f1337,plain,(
% 1.69/0.59    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k1_xboole_0) | (~spl2_8 | ~spl2_26)),
% 1.69/0.59    inference(forward_demodulation,[],[f1335,f160])).
% 1.69/0.59  fof(f160,plain,(
% 1.69/0.59    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.69/0.59    inference(forward_demodulation,[],[f159,f133])).
% 1.69/0.59  fof(f133,plain,(
% 1.69/0.59    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 1.69/0.59    inference(forward_demodulation,[],[f130,f66])).
% 1.69/0.59  fof(f130,plain,(
% 1.69/0.59    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,k3_subset_1(X0,k1_xboole_0))) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f41,f54])).
% 1.69/0.59  fof(f54,plain,(
% 1.69/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.69/0.59    inference(cnf_transformation,[],[f26])).
% 1.69/0.59  fof(f26,plain,(
% 1.69/0.59    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.69/0.59    inference(ennf_transformation,[],[f17])).
% 1.69/0.59  fof(f17,axiom,(
% 1.69/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.69/0.59  fof(f159,plain,(
% 1.69/0.59    ( ! [X0] : (k3_subset_1(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.69/0.59    inference(forward_demodulation,[],[f151,f104])).
% 1.69/0.59  fof(f104,plain,(
% 1.69/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f73,f52])).
% 1.69/0.59  fof(f73,plain,(
% 1.69/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.69/0.59    inference(equality_resolution,[],[f58])).
% 1.69/0.59  fof(f58,plain,(
% 1.69/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.69/0.59    inference(cnf_transformation,[],[f34])).
% 1.69/0.59  fof(f34,plain,(
% 1.69/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.59    inference(flattening,[],[f33])).
% 1.69/0.59  fof(f33,plain,(
% 1.69/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.69/0.59    inference(nnf_transformation,[],[f2])).
% 1.69/0.59  fof(f2,axiom,(
% 1.69/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.69/0.59  fof(f151,plain,(
% 1.69/0.59    ( ! [X0] : (k3_subset_1(X0,X0) = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.69/0.59    inference(unit_resulting_resolution,[],[f77,f72])).
% 1.69/0.59  fof(f77,plain,(
% 1.69/0.59    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.69/0.59    inference(forward_demodulation,[],[f67,f66])).
% 1.69/0.59  fof(f67,plain,(
% 1.69/0.59    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 1.69/0.59    inference(definition_unfolding,[],[f42,f63])).
% 1.69/0.59  fof(f42,plain,(
% 1.69/0.59    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.69/0.59    inference(cnf_transformation,[],[f16])).
% 1.69/0.59  fof(f16,axiom,(
% 1.69/0.59    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.69/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.69/0.59  fof(f1335,plain,(
% 1.69/0.59    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) | (~spl2_8 | ~spl2_26)),
% 1.69/0.59    inference(backward_demodulation,[],[f1081,f1313])).
% 1.69/0.59  fof(f1313,plain,(
% 1.69/0.59    sK1 = k3_xboole_0(sK0,sK1) | ~spl2_26),
% 1.69/0.59    inference(superposition,[],[f1303,f46])).
% 1.69/0.59  fof(f1303,plain,(
% 1.69/0.59    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_26),
% 1.69/0.59    inference(avatar_component_clause,[],[f1301])).
% 1.69/0.59  fof(f1301,plain,(
% 1.69/0.59    spl2_26 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 1.69/0.59    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 1.69/0.59  fof(f1081,plain,(
% 1.69/0.59    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) | ~spl2_8),
% 1.69/0.59    inference(forward_demodulation,[],[f1045,f46])).
% 1.69/0.59  fof(f1045,plain,(
% 1.69/0.59    k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | ~spl2_8),
% 1.69/0.59    inference(superposition,[],[f416,f240])).
% 1.69/0.59  fof(f240,plain,(
% 1.69/0.59    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl2_8),
% 1.69/0.59    inference(avatar_component_clause,[],[f238])).
% 1.69/0.60  fof(f238,plain,(
% 1.69/0.60    spl2_8 <=> k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.69/0.60  fof(f416,plain,(
% 1.69/0.60    ( ! [X6,X7] : (k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6))) = k5_xboole_0(X7,k5_xboole_0(X6,k3_xboole_0(X6,X7)))) )),
% 1.69/0.60    inference(superposition,[],[f165,f71])).
% 1.69/0.60  fof(f71,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k3_tarski(k2_enumset1(X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.69/0.60    inference(definition_unfolding,[],[f50,f62,f51])).
% 1.69/0.60  fof(f62,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_enumset1(X0,X0,X0,X1))) )),
% 1.69/0.60    inference(definition_unfolding,[],[f48,f61])).
% 1.69/0.60  fof(f61,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.69/0.60    inference(definition_unfolding,[],[f49,f60])).
% 1.69/0.60  fof(f60,plain,(
% 1.69/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f11])).
% 1.69/0.60  fof(f11,axiom,(
% 1.69/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.69/0.60  fof(f49,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f10])).
% 1.69/0.60  fof(f10,axiom,(
% 1.69/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.69/0.60  fof(f48,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.69/0.60    inference(cnf_transformation,[],[f12])).
% 1.69/0.60  fof(f12,axiom,(
% 1.69/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.69/0.60  fof(f50,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.69/0.60    inference(cnf_transformation,[],[f8])).
% 1.69/0.60  fof(f8,axiom,(
% 1.69/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.69/0.60  fof(f165,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k3_tarski(k2_enumset1(X1,X1,X1,X0))) )),
% 1.69/0.60    inference(superposition,[],[f71,f69])).
% 1.69/0.60  fof(f69,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_enumset1(X1,X1,X1,X0)) )),
% 1.69/0.60    inference(definition_unfolding,[],[f45,f61,f61])).
% 1.69/0.60  fof(f45,plain,(
% 1.69/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f9])).
% 1.69/0.60  fof(f9,axiom,(
% 1.69/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.69/0.60  fof(f1352,plain,(
% 1.69/0.60    ~r1_tarski(sK1,k5_xboole_0(sK1,k3_subset_1(sK0,sK1))) | (spl2_3 | ~spl2_8 | ~spl2_11 | ~spl2_26)),
% 1.69/0.60    inference(subsumption_resolution,[],[f1341,f89])).
% 1.69/0.60  fof(f89,plain,(
% 1.69/0.60    sK0 != sK1 | spl2_3),
% 1.69/0.60    inference(avatar_component_clause,[],[f88])).
% 1.69/0.60  fof(f88,plain,(
% 1.69/0.60    spl2_3 <=> sK0 = sK1),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.69/0.60  fof(f1341,plain,(
% 1.69/0.60    sK0 = sK1 | ~r1_tarski(sK1,k5_xboole_0(sK1,k3_subset_1(sK0,sK1))) | (~spl2_8 | ~spl2_11 | ~spl2_26)),
% 1.69/0.60    inference(backward_demodulation,[],[f405,f1338])).
% 1.69/0.60  fof(f405,plain,(
% 1.69/0.60    sK1 = k5_xboole_0(sK1,k3_subset_1(sK0,sK1)) | ~r1_tarski(sK1,k5_xboole_0(sK1,k3_subset_1(sK0,sK1))) | ~spl2_11),
% 1.69/0.60    inference(resolution,[],[f325,f59])).
% 1.69/0.60  fof(f59,plain,(
% 1.69/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f34])).
% 1.69/0.60  fof(f325,plain,(
% 1.69/0.60    r1_tarski(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),sK1) | ~spl2_11),
% 1.69/0.60    inference(avatar_component_clause,[],[f323])).
% 1.69/0.60  fof(f323,plain,(
% 1.69/0.60    spl2_11 <=> r1_tarski(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),sK1)),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 1.69/0.60  fof(f1304,plain,(
% 1.69/0.60    spl2_26 | ~spl2_19),
% 1.69/0.60    inference(avatar_split_clause,[],[f711,f611,f1301])).
% 1.69/0.60  fof(f711,plain,(
% 1.69/0.60    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_19),
% 1.69/0.60    inference(unit_resulting_resolution,[],[f613,f52])).
% 1.69/0.60  fof(f614,plain,(
% 1.69/0.60    spl2_19 | ~spl2_1),
% 1.69/0.60    inference(avatar_split_clause,[],[f601,f79,f611])).
% 1.69/0.60  fof(f79,plain,(
% 1.69/0.60    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.69/0.60  fof(f601,plain,(
% 1.69/0.60    r1_tarski(sK1,sK0) | ~spl2_1),
% 1.69/0.60    inference(unit_resulting_resolution,[],[f81,f230])).
% 1.69/0.60  fof(f230,plain,(
% 1.69/0.60    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X2)) | r1_tarski(X3,X2)) )),
% 1.69/0.60    inference(subsumption_resolution,[],[f229,f77])).
% 1.69/0.60  fof(f229,plain,(
% 1.69/0.60    ( ! [X2,X3] : (r1_tarski(X3,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 1.69/0.60    inference(subsumption_resolution,[],[f225,f38])).
% 1.69/0.60  fof(f225,plain,(
% 1.69/0.60    ( ! [X2,X3] : (~r1_tarski(k1_xboole_0,k3_subset_1(X2,X3)) | r1_tarski(X3,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 1.69/0.60    inference(superposition,[],[f56,f133])).
% 1.69/0.60  fof(f56,plain,(
% 1.69/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.69/0.60    inference(cnf_transformation,[],[f32])).
% 1.69/0.60  fof(f32,plain,(
% 1.69/0.60    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.69/0.60    inference(nnf_transformation,[],[f27])).
% 1.69/0.60  fof(f27,plain,(
% 1.69/0.60    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.69/0.60    inference(ennf_transformation,[],[f19])).
% 1.69/0.60  fof(f19,axiom,(
% 1.69/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 1.69/0.60  fof(f81,plain,(
% 1.69/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_1),
% 1.69/0.60    inference(avatar_component_clause,[],[f79])).
% 1.69/0.60  fof(f326,plain,(
% 1.69/0.60    spl2_11 | ~spl2_7),
% 1.69/0.60    inference(avatar_split_clause,[],[f296,f233,f323])).
% 1.69/0.60  fof(f233,plain,(
% 1.69/0.60    spl2_7 <=> k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1)),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.69/0.60  fof(f296,plain,(
% 1.69/0.60    r1_tarski(k5_xboole_0(sK1,k3_subset_1(sK0,sK1)),sK1) | ~spl2_7),
% 1.69/0.60    inference(superposition,[],[f101,f235])).
% 1.69/0.60  fof(f235,plain,(
% 1.69/0.60    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl2_7),
% 1.69/0.60    inference(avatar_component_clause,[],[f233])).
% 1.69/0.60  fof(f101,plain,(
% 1.69/0.60    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X1,X0)),X0)) )),
% 1.69/0.60    inference(superposition,[],[f68,f46])).
% 1.69/0.60  fof(f68,plain,(
% 1.69/0.60    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 1.69/0.60    inference(definition_unfolding,[],[f44,f51])).
% 1.69/0.60  fof(f44,plain,(
% 1.69/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.69/0.60    inference(cnf_transformation,[],[f7])).
% 1.69/0.60  fof(f7,axiom,(
% 1.69/0.60    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.69/0.60  fof(f241,plain,(
% 1.69/0.60    spl2_8 | ~spl2_1),
% 1.69/0.60    inference(avatar_split_clause,[],[f153,f79,f238])).
% 1.69/0.60  fof(f153,plain,(
% 1.69/0.60    k3_subset_1(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | ~spl2_1),
% 1.69/0.60    inference(unit_resulting_resolution,[],[f81,f72])).
% 1.69/0.60  fof(f236,plain,(
% 1.69/0.60    spl2_7 | ~spl2_2),
% 1.69/0.60    inference(avatar_split_clause,[],[f143,f84,f233])).
% 1.69/0.60  fof(f84,plain,(
% 1.69/0.60    spl2_2 <=> r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.69/0.60  fof(f143,plain,(
% 1.69/0.60    k3_subset_1(sK0,sK1) = k3_xboole_0(k3_subset_1(sK0,sK1),sK1) | ~spl2_2),
% 1.69/0.60    inference(unit_resulting_resolution,[],[f86,f52])).
% 1.69/0.60  fof(f86,plain,(
% 1.69/0.60    r1_tarski(k3_subset_1(sK0,sK1),sK1) | ~spl2_2),
% 1.69/0.60    inference(avatar_component_clause,[],[f84])).
% 1.69/0.60  fof(f136,plain,(
% 1.69/0.60    spl2_4),
% 1.69/0.60    inference(avatar_contradiction_clause,[],[f135])).
% 1.69/0.60  fof(f135,plain,(
% 1.69/0.60    $false | spl2_4),
% 1.69/0.60    inference(subsumption_resolution,[],[f134,f38])).
% 1.69/0.60  fof(f134,plain,(
% 1.69/0.60    ~r1_tarski(k1_xboole_0,sK0) | spl2_4),
% 1.69/0.60    inference(backward_demodulation,[],[f99,f133])).
% 1.69/0.60  fof(f99,plain,(
% 1.69/0.60    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | spl2_4),
% 1.69/0.60    inference(avatar_component_clause,[],[f97])).
% 1.69/0.60  fof(f97,plain,(
% 1.69/0.60    spl2_4 <=> r1_tarski(k3_subset_1(sK0,sK0),sK0)),
% 1.69/0.60    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.69/0.60  fof(f100,plain,(
% 1.69/0.60    ~spl2_4 | ~spl2_3),
% 1.69/0.60    inference(avatar_split_clause,[],[f94,f88,f97])).
% 1.69/0.60  fof(f94,plain,(
% 1.69/0.60    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | ~spl2_3),
% 1.69/0.60    inference(subsumption_resolution,[],[f93,f90])).
% 1.69/0.60  fof(f90,plain,(
% 1.69/0.60    sK0 = sK1 | ~spl2_3),
% 1.69/0.60    inference(avatar_component_clause,[],[f88])).
% 1.69/0.60  fof(f93,plain,(
% 1.69/0.60    ~r1_tarski(k3_subset_1(sK0,sK0),sK0) | sK0 != sK1 | ~spl2_3),
% 1.69/0.60    inference(backward_demodulation,[],[f76,f90])).
% 1.69/0.60  fof(f76,plain,(
% 1.69/0.60    sK0 != sK1 | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.69/0.60    inference(backward_demodulation,[],[f64,f66])).
% 1.69/0.60  fof(f64,plain,(
% 1.69/0.60    sK1 != k3_subset_1(sK0,k1_xboole_0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.69/0.60    inference(definition_unfolding,[],[f37,f63])).
% 1.69/0.60  fof(f37,plain,(
% 1.69/0.60    sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.69/0.60    inference(cnf_transformation,[],[f31])).
% 1.69/0.60  fof(f31,plain,(
% 1.69/0.60    (sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.69/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).
% 1.69/0.60  fof(f30,plain,(
% 1.69/0.60    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => ((sK1 != k2_subset_1(sK0) | ~r1_tarski(k3_subset_1(sK0,sK1),sK1)) & (sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.69/0.60    introduced(choice_axiom,[])).
% 1.69/0.60  fof(f29,plain,(
% 1.69/0.60    ? [X0,X1] : ((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.69/0.60    inference(flattening,[],[f28])).
% 1.69/0.60  fof(f28,plain,(
% 1.69/0.60    ? [X0,X1] : (((k2_subset_1(X0) != X1 | ~r1_tarski(k3_subset_1(X0,X1),X1)) & (k2_subset_1(X0) = X1 | r1_tarski(k3_subset_1(X0,X1),X1))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.69/0.60    inference(nnf_transformation,[],[f23])).
% 1.69/0.60  fof(f23,plain,(
% 1.69/0.60    ? [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <~> k2_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.69/0.60    inference(ennf_transformation,[],[f22])).
% 1.69/0.60  fof(f22,negated_conjecture,(
% 1.69/0.60    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.69/0.60    inference(negated_conjecture,[],[f21])).
% 1.69/0.60  fof(f21,conjecture,(
% 1.69/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.69/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).
% 1.69/0.60  fof(f91,plain,(
% 1.69/0.60    spl2_2 | spl2_3),
% 1.69/0.60    inference(avatar_split_clause,[],[f75,f88,f84])).
% 1.69/0.60  fof(f75,plain,(
% 1.69/0.60    sK0 = sK1 | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.69/0.60    inference(backward_demodulation,[],[f65,f66])).
% 1.69/0.60  fof(f65,plain,(
% 1.69/0.60    sK1 = k3_subset_1(sK0,k1_xboole_0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.69/0.60    inference(definition_unfolding,[],[f36,f63])).
% 1.69/0.60  fof(f36,plain,(
% 1.69/0.60    sK1 = k2_subset_1(sK0) | r1_tarski(k3_subset_1(sK0,sK1),sK1)),
% 1.69/0.60    inference(cnf_transformation,[],[f31])).
% 1.69/0.60  fof(f82,plain,(
% 1.69/0.60    spl2_1),
% 1.69/0.60    inference(avatar_split_clause,[],[f35,f79])).
% 1.69/0.60  fof(f35,plain,(
% 1.69/0.60    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.69/0.60    inference(cnf_transformation,[],[f31])).
% 1.69/0.60  % SZS output end Proof for theBenchmark
% 1.69/0.60  % (3163)------------------------------
% 1.69/0.60  % (3163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.69/0.60  % (3163)Termination reason: Refutation
% 1.69/0.60  
% 1.69/0.60  % (3163)Memory used [KB]: 11513
% 1.69/0.60  % (3163)Time elapsed: 0.177 s
% 1.69/0.60  % (3163)------------------------------
% 1.69/0.60  % (3163)------------------------------
% 1.69/0.60  % (3142)Success in time 0.23 s
%------------------------------------------------------------------------------
