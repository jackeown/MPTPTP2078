%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:06 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 198 expanded)
%              Number of leaves         :   30 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :  204 ( 317 expanded)
%              Number of equality atoms :   76 ( 153 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1096,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f104,f124,f316,f511,f523,f606,f1095])).

fof(f1095,plain,
    ( spl5_3
    | ~ spl5_7
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f1094,f433,f130,f101])).

fof(f101,plain,
    ( spl5_3
  <=> sK0 = k4_subset_1(sK0,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f130,plain,
    ( spl5_7
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f433,plain,
    ( spl5_21
  <=> k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1094,plain,
    ( sK0 = k4_subset_1(sK0,sK1,sK0)
    | ~ spl5_7
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f1093,f35])).

fof(f35,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f1093,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl5_7
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f1092,f163])).

fof(f163,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(global_subsumption,[],[f145,f160])).

fof(f160,plain,(
    ! [X0] :
      ( r2_hidden(sK2(k5_xboole_0(X0,X0)),X0)
      | k1_xboole_0 = k5_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f137,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f84,f38])).

fof(f38,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f58,f42])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f145,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(k5_xboole_0(X0,X0)),X0)
      | k1_xboole_0 = k5_xboole_0(X0,X0) ) ),
    inference(resolution,[],[f126,f37])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k5_xboole_0(X0,X0))
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f83,f38])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f59,f42])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1092,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))
    | ~ spl5_7
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f1081,f132])).

fof(f132,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1081,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))
    | ~ spl5_21 ),
    inference(superposition,[],[f72,f435])).

fof(f435,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f433])).

fof(f72,plain,(
    ! [X0,X1] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f43,f70,f42])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f53,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f53,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f606,plain,(
    ~ spl5_4 ),
    inference(avatar_contradiction_clause,[],[f604])).

fof(f604,plain,
    ( $false
    | ~ spl5_4 ),
    inference(resolution,[],[f111,f33])).

fof(f33,plain,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

fof(f111,plain,
    ( v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl5_4
  <=> v1_xboole_0(k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f523,plain,
    ( spl5_21
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f522,f91,f433])).

fof(f91,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f522,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f516,f71])).

fof(f71,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f69,f69])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f516,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f205,f95])).

fof(f95,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f36,f34])).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f205,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k4_subset_1(sK0,sK1,X0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f73,f93])).

fof(f93,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f54,f70])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

% (2642)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f511,plain,
    ( spl5_4
    | spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f509,f91,f113,f109])).

fof(f113,plain,
    ( spl5_5
  <=> r2_hidden(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f509,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | v1_xboole_0(k1_zfmisc_1(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f93,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f316,plain,
    ( spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f314,f121,f130])).

fof(f121,plain,
    ( spl5_6
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f314,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl5_6 ),
    inference(resolution,[],[f123,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f123,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f124,plain,
    ( spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f118,f113,f121])).

fof(f118,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_5 ),
    inference(resolution,[],[f115,f80])).

fof(f80,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_zfmisc_1(X0))
      | r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f115,plain,
    ( r2_hidden(sK1,k1_zfmisc_1(sK0))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f104,plain,
    ( ~ spl5_3
    | spl5_1 ),
    inference(avatar_split_clause,[],[f99,f86,f101])).

fof(f86,plain,
    ( spl5_1
  <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f99,plain,
    ( sK0 != k4_subset_1(sK0,sK1,sK0)
    | spl5_1 ),
    inference(forward_demodulation,[],[f88,f34])).

fof(f88,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f86])).

fof(f94,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f31,f91])).

fof(f31,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f89,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f32,f86])).

fof(f32,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (2634)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.52  % (2618)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (2629)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (2629)Refutation not found, incomplete strategy% (2629)------------------------------
% 0.20/0.52  % (2629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2629)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2629)Memory used [KB]: 10618
% 0.20/0.52  % (2629)Time elapsed: 0.116 s
% 0.20/0.52  % (2629)------------------------------
% 0.20/0.52  % (2629)------------------------------
% 0.20/0.52  % (2626)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (2641)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (2625)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (2622)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (2621)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (2637)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.42/0.55  % (2633)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.42/0.55  % (2635)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.42/0.55  % (2635)Refutation not found, incomplete strategy% (2635)------------------------------
% 1.42/0.55  % (2635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (2635)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (2635)Memory used [KB]: 10618
% 1.42/0.55  % (2635)Time elapsed: 0.146 s
% 1.42/0.55  % (2635)------------------------------
% 1.42/0.55  % (2635)------------------------------
% 1.42/0.55  % (2628)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.42/0.56  % (2620)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.42/0.56  % (2630)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.42/0.56  % (2646)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.42/0.56  % (2640)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.42/0.56  % (2644)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.42/0.56  % (2627)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.42/0.56  % (2640)Refutation not found, incomplete strategy% (2640)------------------------------
% 1.42/0.56  % (2640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (2640)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (2640)Memory used [KB]: 10746
% 1.42/0.56  % (2640)Time elapsed: 0.151 s
% 1.42/0.56  % (2640)------------------------------
% 1.42/0.56  % (2640)------------------------------
% 1.42/0.56  % (2619)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.42/0.56  % (2647)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.57/0.56  % (2623)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.57/0.56  % (2634)Refutation found. Thanks to Tanya!
% 1.57/0.56  % SZS status Theorem for theBenchmark
% 1.57/0.56  % SZS output start Proof for theBenchmark
% 1.57/0.56  fof(f1096,plain,(
% 1.57/0.56    $false),
% 1.57/0.56    inference(avatar_sat_refutation,[],[f89,f94,f104,f124,f316,f511,f523,f606,f1095])).
% 1.57/0.56  fof(f1095,plain,(
% 1.57/0.56    spl5_3 | ~spl5_7 | ~spl5_21),
% 1.57/0.56    inference(avatar_split_clause,[],[f1094,f433,f130,f101])).
% 1.57/0.56  fof(f101,plain,(
% 1.57/0.56    spl5_3 <=> sK0 = k4_subset_1(sK0,sK1,sK0)),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.57/0.56  fof(f130,plain,(
% 1.57/0.56    spl5_7 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.57/0.56  fof(f433,plain,(
% 1.57/0.56    spl5_21 <=> k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.57/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.57/0.57  fof(f1094,plain,(
% 1.57/0.57    sK0 = k4_subset_1(sK0,sK1,sK0) | (~spl5_7 | ~spl5_21)),
% 1.57/0.57    inference(forward_demodulation,[],[f1093,f35])).
% 1.57/0.57  fof(f35,plain,(
% 1.57/0.57    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f6])).
% 1.57/0.57  fof(f6,axiom,(
% 1.57/0.57    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.57/0.57  fof(f1093,plain,(
% 1.57/0.57    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k1_xboole_0) | (~spl5_7 | ~spl5_21)),
% 1.57/0.57    inference(forward_demodulation,[],[f1092,f163])).
% 1.57/0.57  fof(f163,plain,(
% 1.57/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.57/0.57    inference(global_subsumption,[],[f145,f160])).
% 1.57/0.57  fof(f160,plain,(
% 1.57/0.57    ( ! [X0] : (r2_hidden(sK2(k5_xboole_0(X0,X0)),X0) | k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.57/0.57    inference(resolution,[],[f137,f37])).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.57/0.57    inference(ennf_transformation,[],[f3])).
% 1.57/0.57  fof(f3,axiom,(
% 1.57/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.57/0.57  fof(f137,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | r2_hidden(X1,X0)) )),
% 1.57/0.57    inference(superposition,[],[f84,f38])).
% 1.57/0.57  fof(f38,plain,(
% 1.57/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f24])).
% 1.57/0.57  fof(f24,plain,(
% 1.57/0.57    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.57/0.57    inference(rectify,[],[f2])).
% 1.57/0.57  fof(f2,axiom,(
% 1.57/0.57    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.57/0.57  fof(f84,plain,(
% 1.57/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | r2_hidden(X3,X0)) )),
% 1.57/0.57    inference(equality_resolution,[],[f76])).
% 1.57/0.57  fof(f76,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.57/0.57    inference(definition_unfolding,[],[f58,f42])).
% 1.57/0.57  fof(f42,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f4])).
% 1.57/0.57  fof(f4,axiom,(
% 1.57/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.57/0.57  fof(f58,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.57/0.57    inference(cnf_transformation,[],[f1])).
% 1.57/0.57  fof(f1,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.57/0.57  fof(f145,plain,(
% 1.57/0.57    ( ! [X0] : (~r2_hidden(sK2(k5_xboole_0(X0,X0)),X0) | k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.57/0.57    inference(resolution,[],[f126,f37])).
% 1.57/0.57  fof(f126,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r2_hidden(X1,k5_xboole_0(X0,X0)) | ~r2_hidden(X1,X0)) )),
% 1.57/0.57    inference(superposition,[],[f83,f38])).
% 1.57/0.57  fof(f83,plain,(
% 1.57/0.57    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | ~r2_hidden(X3,X1)) )),
% 1.57/0.57    inference(equality_resolution,[],[f75])).
% 1.57/0.57  fof(f75,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.57/0.57    inference(definition_unfolding,[],[f59,f42])).
% 1.57/0.57  fof(f59,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.57/0.57    inference(cnf_transformation,[],[f1])).
% 1.57/0.57  fof(f1092,plain,(
% 1.57/0.57    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) | (~spl5_7 | ~spl5_21)),
% 1.57/0.57    inference(forward_demodulation,[],[f1081,f132])).
% 1.57/0.57  fof(f132,plain,(
% 1.57/0.57    sK1 = k3_xboole_0(sK1,sK0) | ~spl5_7),
% 1.57/0.57    inference(avatar_component_clause,[],[f130])).
% 1.57/0.57  fof(f1081,plain,(
% 1.57/0.57    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))) | ~spl5_21),
% 1.57/0.57    inference(superposition,[],[f72,f435])).
% 1.57/0.57  fof(f435,plain,(
% 1.57/0.57    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_21),
% 1.57/0.57    inference(avatar_component_clause,[],[f433])).
% 1.57/0.57  fof(f72,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.57/0.57    inference(definition_unfolding,[],[f43,f70,f42])).
% 1.57/0.57  fof(f70,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.57/0.57    inference(definition_unfolding,[],[f40,f69])).
% 1.57/0.57  fof(f69,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f41,f68])).
% 1.57/0.57  fof(f68,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f53,f67])).
% 1.57/0.57  fof(f67,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f61,f66])).
% 1.57/0.57  fof(f66,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f62,f65])).
% 1.57/0.57  fof(f65,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f63,f64])).
% 1.57/0.57  fof(f64,plain,(
% 1.57/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f14])).
% 1.57/0.57  fof(f14,axiom,(
% 1.57/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.57/0.57  fof(f63,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f13])).
% 1.57/0.57  fof(f13,axiom,(
% 1.57/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.57/0.57  fof(f62,plain,(
% 1.57/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f12])).
% 1.57/0.57  fof(f12,axiom,(
% 1.57/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.57/0.57  fof(f61,plain,(
% 1.57/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f11])).
% 1.57/0.57  fof(f11,axiom,(
% 1.57/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.57/0.57  fof(f53,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f10])).
% 1.57/0.57  fof(f10,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.57/0.57  fof(f41,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f9])).
% 1.57/0.57  fof(f9,axiom,(
% 1.57/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.57/0.57  fof(f40,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f16])).
% 1.57/0.57  fof(f16,axiom,(
% 1.57/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.57/0.57  fof(f43,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f7])).
% 1.57/0.57  fof(f7,axiom,(
% 1.57/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.57/0.57  fof(f606,plain,(
% 1.57/0.57    ~spl5_4),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f604])).
% 1.57/0.57  fof(f604,plain,(
% 1.57/0.57    $false | ~spl5_4),
% 1.57/0.57    inference(resolution,[],[f111,f33])).
% 1.57/0.57  fof(f33,plain,(
% 1.57/0.57    ( ! [X0] : (~v1_xboole_0(k1_zfmisc_1(X0))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f20])).
% 1.57/0.57  fof(f20,axiom,(
% 1.57/0.57    ! [X0] : ~v1_xboole_0(k1_zfmisc_1(X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).
% 1.57/0.57  fof(f111,plain,(
% 1.57/0.57    v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_4),
% 1.57/0.57    inference(avatar_component_clause,[],[f109])).
% 1.57/0.57  fof(f109,plain,(
% 1.57/0.57    spl5_4 <=> v1_xboole_0(k1_zfmisc_1(sK0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.57/0.57  fof(f523,plain,(
% 1.57/0.57    spl5_21 | ~spl5_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f522,f91,f433])).
% 1.57/0.57  fof(f91,plain,(
% 1.57/0.57    spl5_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.57/0.57  fof(f522,plain,(
% 1.57/0.57    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_2),
% 1.57/0.57    inference(forward_demodulation,[],[f516,f71])).
% 1.57/0.57  fof(f71,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.57/0.57    inference(definition_unfolding,[],[f39,f69,f69])).
% 1.57/0.57  fof(f39,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f8])).
% 1.57/0.57  fof(f8,axiom,(
% 1.57/0.57    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.57/0.57  fof(f516,plain,(
% 1.57/0.57    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK0)) | ~spl5_2),
% 1.57/0.57    inference(resolution,[],[f205,f95])).
% 1.57/0.57  fof(f95,plain,(
% 1.57/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.57/0.57    inference(forward_demodulation,[],[f36,f34])).
% 1.57/0.57  fof(f34,plain,(
% 1.57/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f18])).
% 1.57/0.57  fof(f18,axiom,(
% 1.57/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.57/0.57  fof(f36,plain,(
% 1.57/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f19])).
% 1.57/0.57  fof(f19,axiom,(
% 1.57/0.57    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.57/0.57  fof(f205,plain,(
% 1.57/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) ) | ~spl5_2),
% 1.57/0.57    inference(resolution,[],[f73,f93])).
% 1.57/0.57  fof(f93,plain,(
% 1.57/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.57/0.57    inference(avatar_component_clause,[],[f91])).
% 1.57/0.57  fof(f73,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 1.57/0.57    inference(definition_unfolding,[],[f54,f70])).
% 1.57/0.57  fof(f54,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f30])).
% 1.57/0.57  fof(f30,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(flattening,[],[f29])).
% 1.57/0.57  fof(f29,plain,(
% 1.57/0.57    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.57/0.57    inference(ennf_transformation,[],[f21])).
% 1.57/0.57  % (2642)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.57/0.57  fof(f21,axiom,(
% 1.57/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.57/0.57  fof(f511,plain,(
% 1.57/0.57    spl5_4 | spl5_5 | ~spl5_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f509,f91,f113,f109])).
% 1.57/0.57  fof(f113,plain,(
% 1.57/0.57    spl5_5 <=> r2_hidden(sK1,k1_zfmisc_1(sK0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.57/0.57  fof(f509,plain,(
% 1.57/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | v1_xboole_0(k1_zfmisc_1(sK0)) | ~spl5_2),
% 1.57/0.57    inference(resolution,[],[f93,f47])).
% 1.57/0.57  fof(f47,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f27])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f17])).
% 1.57/0.57  fof(f17,axiom,(
% 1.57/0.57    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.57/0.57  fof(f316,plain,(
% 1.57/0.57    spl5_7 | ~spl5_6),
% 1.57/0.57    inference(avatar_split_clause,[],[f314,f121,f130])).
% 1.57/0.57  fof(f121,plain,(
% 1.57/0.57    spl5_6 <=> r1_tarski(sK1,sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.57/0.57  fof(f314,plain,(
% 1.57/0.57    sK1 = k3_xboole_0(sK1,sK0) | ~spl5_6),
% 1.57/0.57    inference(resolution,[],[f123,f48])).
% 1.57/0.57  fof(f48,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f28])).
% 1.57/0.57  fof(f28,plain,(
% 1.57/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.57/0.57    inference(ennf_transformation,[],[f5])).
% 1.57/0.57  fof(f5,axiom,(
% 1.57/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.57/0.57  fof(f123,plain,(
% 1.57/0.57    r1_tarski(sK1,sK0) | ~spl5_6),
% 1.57/0.57    inference(avatar_component_clause,[],[f121])).
% 1.57/0.57  fof(f124,plain,(
% 1.57/0.57    spl5_6 | ~spl5_5),
% 1.57/0.57    inference(avatar_split_clause,[],[f118,f113,f121])).
% 1.57/0.57  fof(f118,plain,(
% 1.57/0.57    r1_tarski(sK1,sK0) | ~spl5_5),
% 1.57/0.57    inference(resolution,[],[f115,f80])).
% 1.57/0.57  fof(f80,plain,(
% 1.57/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k1_zfmisc_1(X0)) | r1_tarski(X2,X0)) )),
% 1.57/0.57    inference(equality_resolution,[],[f50])).
% 1.57/0.57  fof(f50,plain,(
% 1.57/0.57    ( ! [X2,X0,X1] : (r1_tarski(X2,X0) | ~r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 1.57/0.57    inference(cnf_transformation,[],[f15])).
% 1.57/0.57  fof(f15,axiom,(
% 1.57/0.57    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.57/0.57  fof(f115,plain,(
% 1.57/0.57    r2_hidden(sK1,k1_zfmisc_1(sK0)) | ~spl5_5),
% 1.57/0.57    inference(avatar_component_clause,[],[f113])).
% 1.57/0.57  fof(f104,plain,(
% 1.57/0.57    ~spl5_3 | spl5_1),
% 1.57/0.57    inference(avatar_split_clause,[],[f99,f86,f101])).
% 1.57/0.57  fof(f86,plain,(
% 1.57/0.57    spl5_1 <=> k2_subset_1(sK0) = k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.57/0.57  fof(f99,plain,(
% 1.57/0.57    sK0 != k4_subset_1(sK0,sK1,sK0) | spl5_1),
% 1.57/0.57    inference(forward_demodulation,[],[f88,f34])).
% 1.57/0.57  fof(f88,plain,(
% 1.57/0.57    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) | spl5_1),
% 1.57/0.57    inference(avatar_component_clause,[],[f86])).
% 1.57/0.57  fof(f94,plain,(
% 1.57/0.57    spl5_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f31,f91])).
% 1.57/0.57  fof(f31,plain,(
% 1.57/0.57    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.57/0.57    inference(cnf_transformation,[],[f25])).
% 1.57/0.57  fof(f25,plain,(
% 1.57/0.57    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.57/0.57    inference(ennf_transformation,[],[f23])).
% 1.57/0.57  fof(f23,negated_conjecture,(
% 1.57/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.57/0.57    inference(negated_conjecture,[],[f22])).
% 1.57/0.57  fof(f22,conjecture,(
% 1.57/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.57/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 1.57/0.57  fof(f89,plain,(
% 1.57/0.57    ~spl5_1),
% 1.57/0.57    inference(avatar_split_clause,[],[f32,f86])).
% 1.57/0.57  fof(f32,plain,(
% 1.57/0.57    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.57/0.57    inference(cnf_transformation,[],[f25])).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (2634)------------------------------
% 1.57/0.57  % (2634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (2634)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (2634)Memory used [KB]: 11513
% 1.57/0.57  % (2634)Time elapsed: 0.156 s
% 1.57/0.57  % (2634)------------------------------
% 1.57/0.57  % (2634)------------------------------
% 1.57/0.57  % (2617)Success in time 0.213 s
%------------------------------------------------------------------------------
