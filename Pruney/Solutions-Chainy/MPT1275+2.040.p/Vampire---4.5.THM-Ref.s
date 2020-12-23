%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:48 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 343 expanded)
%              Number of leaves         :   31 ( 104 expanded)
%              Depth                    :   21
%              Number of atoms          :  381 (1532 expanded)
%              Number of equality atoms :  100 ( 418 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2654)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
fof(f430,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f109,f203,f247,f276,f417,f429])).

fof(f429,plain,
    ( spl2_4
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f428,f101,f200])).

fof(f200,plain,
    ( spl2_4
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f101,plain,
    ( spl2_1
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f428,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(subsumption_resolution,[],[f427,f102])).

fof(f102,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f427,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ v3_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f134,f55])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,
    ( ( sK1 != k2_tops_1(sK0,sK1)
      | ~ v3_tops_1(sK1,sK0) )
    & ( sK1 = k2_tops_1(sK0,sK1)
      | v3_tops_1(sK1,sK0) )
    & v4_pre_topc(sK1,sK0)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).

fof(f48,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != X1
              | ~ v3_tops_1(X1,X0) )
            & ( k2_tops_1(X0,X1) = X1
              | v3_tops_1(X1,X0) )
            & v4_pre_topc(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != X1
            | ~ v3_tops_1(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = X1
            | v3_tops_1(X1,sK0) )
          & v4_pre_topc(X1,sK0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != X1
          | ~ v3_tops_1(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = X1
          | v3_tops_1(X1,sK0) )
        & v4_pre_topc(X1,sK0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( sK1 != k2_tops_1(sK0,sK1)
        | ~ v3_tops_1(sK1,sK0) )
      & ( sK1 = k2_tops_1(sK0,sK1)
        | v3_tops_1(sK1,sK0) )
      & v4_pre_topc(sK1,sK0)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != X1
            | ~ v3_tops_1(X1,X0) )
          & ( k2_tops_1(X0,X1) = X1
            | v3_tops_1(X1,X0) )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tops_1(X1,X0)
          <~> k2_tops_1(X0,X1) = X1 )
          & v4_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => ( v3_tops_1(X1,X0)
              <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
           => ( v3_tops_1(X1,X0)
            <=> k2_tops_1(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).

fof(f134,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v3_tops_1(sK1,sK0) ),
    inference(resolution,[],[f127,f111])).

fof(f111,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f81,f56])).

fof(f56,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f50])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f127,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,u1_struct_0(X2))
      | v2_tops_1(X1,X2)
      | ~ l1_pre_topc(X2)
      | ~ v3_tops_1(X1,X2) ) ),
    inference(resolution,[],[f67,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tops_1(X1,X0)
          | ~ v3_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tops_1(X1,X0)
           => v2_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).

fof(f417,plain,
    ( spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f415,f107])).

fof(f107,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl2_2
  <=> sK1 = k2_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f415,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f414,f142])).

fof(f142,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(subsumption_resolution,[],[f140,f62])).

fof(f62,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f140,plain,(
    ! [X0] :
      ( k3_subset_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(resolution,[],[f139,f60])).

fof(f60,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k3_subset_1(X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f137,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f137,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k3_subset_1(X0,X1))
      | k3_subset_1(X0,X1) = X0
      | ~ m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f135,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | X0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f79,f61])).

fof(f61,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_subset_1(X0) = X1
      | ~ r1_tarski(k3_subset_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( r1_tarski(k3_subset_1(X0,X1),X1)
          | k2_subset_1(X0) != X1 )
        & ( k2_subset_1(X0) = X1
          | ~ r1_tarski(k3_subset_1(X0,X1),X1) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(k3_subset_1(X0,X1),X1)
      <=> k2_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

fof(f414,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0)
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f413,f62])).

fof(f413,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f386,f56])).

fof(f386,plain,
    ( k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1))
    | ~ spl2_3 ),
    inference(superposition,[],[f332,f364])).

fof(f364,plain,(
    ! [X6,X4,X5] :
      ( k3_subset_1(X4,X5) = k7_subset_1(X6,X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) ) ),
    inference(superposition,[],[f98,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f77,f96])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f75,f95])).

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f73,f94])).

fof(f94,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f74,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f83,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f86,f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f87,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f88,f89])).

fof(f89,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f88,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f87,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f86,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f83,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f74,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f84,f96])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f332,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f331,f198])).

fof(f198,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl2_3
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f331,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f330,f55])).

fof(f330,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f316,f56])).

fof(f316,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(superposition,[],[f64,f184])).

fof(f184,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f183,f55])).

fof(f183,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f182,f57])).

fof(f57,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f182,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f65,f56])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f64,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f276,plain,
    ( spl2_1
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f275,f200,f101])).

fof(f275,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f271,f55])).

fof(f271,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f270,f201])).

fof(f201,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f200])).

fof(f270,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f268,f57])).

fof(f268,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | ~ v2_tops_1(sK1,sK0)
    | v3_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f68,f56])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | ~ v2_tops_1(X1,X0)
      | v3_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tops_1(X1,X0)
          | ~ v4_pre_topc(X1,X0)
          | ~ v2_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v4_pre_topc(X1,X0)
              & v2_tops_1(X1,X0) )
           => v3_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).

fof(f247,plain,
    ( spl2_4
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f246,f105,f200])).

fof(f246,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f245,f113])).

fof(f113,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(resolution,[],[f81,f110])).

fof(f110,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f63,f61])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f245,plain,
    ( ~ r1_tarski(sK1,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f244,f106])).

fof(f106,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f105])).

fof(f244,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f237,f55])).

fof(f237,plain,
    ( ~ r1_tarski(sK1,k2_tops_1(sK0,sK1))
    | v2_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f72,f56])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,k2_tops_1(X0,X1))
      | v2_tops_1(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ r1_tarski(X1,k2_tops_1(X0,X1)) )
            & ( r1_tarski(X1,k2_tops_1(X0,X1))
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> r1_tarski(X1,k2_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).

fof(f203,plain,
    ( spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f194,f200,f196])).

fof(f194,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f193,f55])).

fof(f193,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f69,f56])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tops_1(X1,X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | k1_xboole_0 != k1_tops_1(X0,X1) )
            & ( k1_xboole_0 = k1_tops_1(X0,X1)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

% (2646)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f109,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f58,f105,f101])).

fof(f58,plain,
    ( sK1 = k2_tops_1(sK0,sK1)
    | v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).

fof(f108,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f59,f105,f101])).

fof(f59,plain,
    ( sK1 != k2_tops_1(sK0,sK1)
    | ~ v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:56:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.53  % (2645)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (2645)Refutation not found, incomplete strategy% (2645)------------------------------
% 0.20/0.54  % (2645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (2645)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (2645)Memory used [KB]: 10746
% 0.20/0.54  % (2645)Time elapsed: 0.115 s
% 0.20/0.54  % (2645)------------------------------
% 0.20/0.54  % (2645)------------------------------
% 0.20/0.55  % (2648)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.37/0.55  % (2670)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.55  % (2664)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.57  % (2664)Refutation not found, incomplete strategy% (2664)------------------------------
% 1.37/0.57  % (2664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.57  % (2664)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.57  
% 1.37/0.57  % (2664)Memory used [KB]: 1791
% 1.37/0.57  % (2664)Time elapsed: 0.134 s
% 1.37/0.57  % (2664)------------------------------
% 1.37/0.57  % (2664)------------------------------
% 1.37/0.57  % (2649)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.62/0.57  % (2643)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.62/0.57  % (2653)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.62/0.58  % (2653)Refutation not found, incomplete strategy% (2653)------------------------------
% 1.62/0.58  % (2653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (2653)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.58  
% 1.62/0.58  % (2653)Memory used [KB]: 10618
% 1.62/0.58  % (2653)Time elapsed: 0.152 s
% 1.62/0.58  % (2653)------------------------------
% 1.62/0.58  % (2653)------------------------------
% 1.62/0.58  % (2656)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.62/0.58  % (2670)Refutation found. Thanks to Tanya!
% 1.62/0.58  % SZS status Theorem for theBenchmark
% 1.62/0.58  % SZS output start Proof for theBenchmark
% 1.62/0.58  % (2654)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.62/0.58  fof(f430,plain,(
% 1.62/0.58    $false),
% 1.62/0.58    inference(avatar_sat_refutation,[],[f108,f109,f203,f247,f276,f417,f429])).
% 1.62/0.58  fof(f429,plain,(
% 1.62/0.58    spl2_4 | ~spl2_1),
% 1.62/0.58    inference(avatar_split_clause,[],[f428,f101,f200])).
% 1.62/0.58  fof(f200,plain,(
% 1.62/0.58    spl2_4 <=> v2_tops_1(sK1,sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.62/0.58  fof(f101,plain,(
% 1.62/0.58    spl2_1 <=> v3_tops_1(sK1,sK0)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.62/0.58  fof(f428,plain,(
% 1.62/0.58    v2_tops_1(sK1,sK0) | ~spl2_1),
% 1.62/0.58    inference(subsumption_resolution,[],[f427,f102])).
% 1.62/0.58  fof(f102,plain,(
% 1.62/0.58    v3_tops_1(sK1,sK0) | ~spl2_1),
% 1.62/0.58    inference(avatar_component_clause,[],[f101])).
% 1.62/0.58  fof(f427,plain,(
% 1.62/0.58    v2_tops_1(sK1,sK0) | ~v3_tops_1(sK1,sK0)),
% 1.62/0.58    inference(subsumption_resolution,[],[f134,f55])).
% 1.62/0.58  fof(f55,plain,(
% 1.62/0.58    l1_pre_topc(sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f50])).
% 1.62/0.58  fof(f50,plain,(
% 1.62/0.58    ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.62/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f47,f49,f48])).
% 1.62/0.58  fof(f48,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f49,plain,(
% 1.62/0.58    ? [X1] : ((k2_tops_1(sK0,X1) != X1 | ~v3_tops_1(X1,sK0)) & (k2_tops_1(sK0,X1) = X1 | v3_tops_1(X1,sK0)) & v4_pre_topc(X1,sK0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)) & (sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)) & v4_pre_topc(sK1,sK0) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.62/0.58    introduced(choice_axiom,[])).
% 1.62/0.58  fof(f47,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0)) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.62/0.58    inference(flattening,[],[f46])).
% 1.62/0.58  fof(f46,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != X1 | ~v3_tops_1(X1,X0)) & (k2_tops_1(X0,X1) = X1 | v3_tops_1(X1,X0))) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.62/0.58    inference(nnf_transformation,[],[f29])).
% 1.62/0.58  fof(f29,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : ((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.62/0.58    inference(flattening,[],[f28])).
% 1.62/0.58  fof(f28,plain,(
% 1.62/0.58    ? [X0] : (? [X1] : (((v3_tops_1(X1,X0) <~> k2_tops_1(X0,X1) = X1) & v4_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f27])).
% 1.62/0.58  fof(f27,negated_conjecture,(
% 1.62/0.58    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 1.62/0.58    inference(negated_conjecture,[],[f26])).
% 1.62/0.58  fof(f26,conjecture,(
% 1.62/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => (v3_tops_1(X1,X0) <=> k2_tops_1(X0,X1) = X1))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_tops_1)).
% 1.62/0.58  fof(f134,plain,(
% 1.62/0.58    v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~v3_tops_1(sK1,sK0)),
% 1.62/0.58    inference(resolution,[],[f127,f111])).
% 1.62/0.58  fof(f111,plain,(
% 1.62/0.58    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.62/0.58    inference(resolution,[],[f81,f56])).
% 1.62/0.58  fof(f56,plain,(
% 1.62/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.62/0.58    inference(cnf_transformation,[],[f50])).
% 1.62/0.58  fof(f81,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f54])).
% 1.62/0.58  fof(f54,plain,(
% 1.62/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.62/0.58    inference(nnf_transformation,[],[f18])).
% 1.62/0.58  fof(f18,axiom,(
% 1.62/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.62/0.58  fof(f127,plain,(
% 1.62/0.58    ( ! [X2,X1] : (~r1_tarski(X1,u1_struct_0(X2)) | v2_tops_1(X1,X2) | ~l1_pre_topc(X2) | ~v3_tops_1(X1,X2)) )),
% 1.62/0.58    inference(resolution,[],[f67,f82])).
% 1.62/0.58  fof(f82,plain,(
% 1.62/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f54])).
% 1.62/0.58  fof(f67,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tops_1(X1,X0) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f34])).
% 1.62/0.58  fof(f34,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(flattening,[],[f33])).
% 1.62/0.58  fof(f33,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) | ~v3_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f24])).
% 1.62/0.58  fof(f24,axiom,(
% 1.62/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tops_1(X1,X0) => v2_tops_1(X1,X0))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_tops_1)).
% 1.62/0.58  fof(f417,plain,(
% 1.62/0.58    spl2_2 | ~spl2_3),
% 1.62/0.58    inference(avatar_contradiction_clause,[],[f416])).
% 1.62/0.58  fof(f416,plain,(
% 1.62/0.58    $false | (spl2_2 | ~spl2_3)),
% 1.62/0.58    inference(subsumption_resolution,[],[f415,f107])).
% 1.62/0.58  fof(f107,plain,(
% 1.62/0.58    sK1 != k2_tops_1(sK0,sK1) | spl2_2),
% 1.62/0.58    inference(avatar_component_clause,[],[f105])).
% 1.62/0.58  fof(f105,plain,(
% 1.62/0.58    spl2_2 <=> sK1 = k2_tops_1(sK0,sK1)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.62/0.58  fof(f415,plain,(
% 1.62/0.58    sK1 = k2_tops_1(sK0,sK1) | ~spl2_3),
% 1.62/0.58    inference(forward_demodulation,[],[f414,f142])).
% 1.62/0.58  fof(f142,plain,(
% 1.62/0.58    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f140,f62])).
% 1.62/0.58  fof(f62,plain,(
% 1.62/0.58    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f16])).
% 1.62/0.58  fof(f16,axiom,(
% 1.62/0.58    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 1.62/0.58  fof(f140,plain,(
% 1.62/0.58    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(resolution,[],[f139,f60])).
% 1.62/0.58  fof(f60,plain,(
% 1.62/0.58    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f2])).
% 1.62/0.58  fof(f2,axiom,(
% 1.62/0.58    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.62/0.58  fof(f139,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k3_subset_1(X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(subsumption_resolution,[],[f137,f76])).
% 1.62/0.58  fof(f76,plain,(
% 1.62/0.58    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f39])).
% 1.62/0.58  fof(f39,plain,(
% 1.62/0.58    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f12])).
% 1.62/0.58  fof(f12,axiom,(
% 1.62/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.62/0.58  fof(f137,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_tarski(X1,k3_subset_1(X0,X1)) | k3_subset_1(X0,X1) = X0 | ~m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(superposition,[],[f135,f78])).
% 1.62/0.58  fof(f78,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f41])).
% 1.62/0.58  fof(f41,plain,(
% 1.62/0.58    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f13])).
% 1.62/0.58  fof(f13,axiom,(
% 1.62/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.62/0.58  fof(f135,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~r1_tarski(k3_subset_1(X0,X1),X1) | X0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(forward_demodulation,[],[f79,f61])).
% 1.62/0.58  fof(f61,plain,(
% 1.62/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.62/0.58    inference(cnf_transformation,[],[f9])).
% 1.62/0.58  fof(f9,axiom,(
% 1.62/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.62/0.58  fof(f79,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f53])).
% 1.62/0.58  fof(f53,plain,(
% 1.62/0.58    ! [X0,X1] : (((r1_tarski(k3_subset_1(X0,X1),X1) | k2_subset_1(X0) != X1) & (k2_subset_1(X0) = X1 | ~r1_tarski(k3_subset_1(X0,X1),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.58    inference(nnf_transformation,[],[f42])).
% 1.62/0.58  fof(f42,plain,(
% 1.62/0.58    ! [X0,X1] : ((r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f15])).
% 1.62/0.58  fof(f15,axiom,(
% 1.62/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(k3_subset_1(X0,X1),X1) <=> k2_subset_1(X0) = X1))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).
% 1.62/0.58  fof(f414,plain,(
% 1.62/0.58    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0) | ~spl2_3),
% 1.62/0.58    inference(subsumption_resolution,[],[f413,f62])).
% 1.62/0.58  fof(f413,plain,(
% 1.62/0.58    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~spl2_3),
% 1.62/0.58    inference(subsumption_resolution,[],[f386,f56])).
% 1.62/0.58  fof(f386,plain,(
% 1.62/0.58    k2_tops_1(sK0,sK1) = k3_subset_1(sK1,k1_xboole_0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK1)) | ~spl2_3),
% 1.62/0.58    inference(superposition,[],[f332,f364])).
% 1.62/0.58  fof(f364,plain,(
% 1.62/0.58    ( ! [X6,X4,X5] : (k3_subset_1(X4,X5) = k7_subset_1(X6,X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(X6)) | ~m1_subset_1(X5,k1_zfmisc_1(X4))) )),
% 1.62/0.58    inference(superposition,[],[f98,f97])).
% 1.62/0.58  fof(f97,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f77,f96])).
% 1.62/0.58  fof(f96,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f75,f95])).
% 1.62/0.58  fof(f95,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f73,f94])).
% 1.62/0.58  fof(f94,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f74,f93])).
% 1.62/0.58  fof(f93,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f83,f92])).
% 1.62/0.58  fof(f92,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f86,f91])).
% 1.62/0.58  fof(f91,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f87,f90])).
% 1.62/0.58  fof(f90,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.62/0.58    inference(definition_unfolding,[],[f88,f89])).
% 1.62/0.58  fof(f89,plain,(
% 1.62/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f8])).
% 1.62/0.58  fof(f8,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.62/0.58  fof(f88,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f7])).
% 1.62/0.58  fof(f7,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.62/0.58  fof(f87,plain,(
% 1.62/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f6])).
% 1.62/0.58  fof(f6,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.62/0.58  fof(f86,plain,(
% 1.62/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f5])).
% 1.62/0.58  fof(f5,axiom,(
% 1.62/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.62/0.58  fof(f83,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f4])).
% 1.62/0.58  fof(f4,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.62/0.58  fof(f74,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f3])).
% 1.62/0.58  fof(f3,axiom,(
% 1.62/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.62/0.58  fof(f73,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f17])).
% 1.62/0.58  fof(f17,axiom,(
% 1.62/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.62/0.58  fof(f75,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f1])).
% 1.62/0.58  fof(f1,axiom,(
% 1.62/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.62/0.58  fof(f77,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f40])).
% 1.62/0.58  fof(f40,plain,(
% 1.62/0.58    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f10])).
% 1.62/0.58  fof(f10,axiom,(
% 1.62/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 1.62/0.58  fof(f98,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(definition_unfolding,[],[f84,f96])).
% 1.62/0.58  fof(f84,plain,(
% 1.62/0.58    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f43])).
% 1.62/0.58  fof(f43,plain,(
% 1.62/0.58    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.62/0.58    inference(ennf_transformation,[],[f14])).
% 1.62/0.58  fof(f14,axiom,(
% 1.62/0.58    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.62/0.58  fof(f332,plain,(
% 1.62/0.58    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) | ~spl2_3),
% 1.62/0.58    inference(forward_demodulation,[],[f331,f198])).
% 1.62/0.58  fof(f198,plain,(
% 1.62/0.58    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl2_3),
% 1.62/0.58    inference(avatar_component_clause,[],[f196])).
% 1.62/0.58  fof(f196,plain,(
% 1.62/0.58    spl2_3 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.62/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.62/0.58  fof(f331,plain,(
% 1.62/0.58    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1))),
% 1.62/0.58    inference(subsumption_resolution,[],[f330,f55])).
% 1.62/0.58  fof(f330,plain,(
% 1.62/0.58    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~l1_pre_topc(sK0)),
% 1.62/0.58    inference(subsumption_resolution,[],[f316,f56])).
% 1.62/0.58  fof(f316,plain,(
% 1.62/0.58    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),sK1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 1.62/0.58    inference(superposition,[],[f64,f184])).
% 1.62/0.58  fof(f184,plain,(
% 1.62/0.58    sK1 = k2_pre_topc(sK0,sK1)),
% 1.62/0.58    inference(subsumption_resolution,[],[f183,f55])).
% 1.62/0.58  fof(f183,plain,(
% 1.62/0.58    sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.62/0.58    inference(subsumption_resolution,[],[f182,f57])).
% 1.62/0.58  fof(f57,plain,(
% 1.62/0.58    v4_pre_topc(sK1,sK0)),
% 1.62/0.58    inference(cnf_transformation,[],[f50])).
% 1.62/0.58  fof(f182,plain,(
% 1.62/0.58    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.62/0.58    inference(resolution,[],[f65,f56])).
% 1.62/0.58  fof(f65,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~l1_pre_topc(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f32])).
% 1.62/0.58  fof(f32,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(flattening,[],[f31])).
% 1.62/0.58  fof(f31,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f20])).
% 1.62/0.58  fof(f20,axiom,(
% 1.62/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.62/0.58  fof(f64,plain,(
% 1.62/0.58    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f30])).
% 1.62/0.58  fof(f30,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f21])).
% 1.62/0.58  fof(f21,axiom,(
% 1.62/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 1.62/0.58  fof(f276,plain,(
% 1.62/0.58    spl2_1 | ~spl2_4),
% 1.62/0.58    inference(avatar_split_clause,[],[f275,f200,f101])).
% 1.62/0.58  fof(f275,plain,(
% 1.62/0.58    v3_tops_1(sK1,sK0) | ~spl2_4),
% 1.62/0.58    inference(subsumption_resolution,[],[f271,f55])).
% 1.62/0.58  fof(f271,plain,(
% 1.62/0.58    v3_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~spl2_4),
% 1.62/0.58    inference(subsumption_resolution,[],[f270,f201])).
% 1.62/0.58  fof(f201,plain,(
% 1.62/0.58    v2_tops_1(sK1,sK0) | ~spl2_4),
% 1.62/0.58    inference(avatar_component_clause,[],[f200])).
% 1.62/0.58  fof(f270,plain,(
% 1.62/0.58    ~v2_tops_1(sK1,sK0) | v3_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.62/0.58    inference(subsumption_resolution,[],[f268,f57])).
% 1.62/0.58  fof(f268,plain,(
% 1.62/0.58    ~v4_pre_topc(sK1,sK0) | ~v2_tops_1(sK1,sK0) | v3_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.62/0.58    inference(resolution,[],[f68,f56])).
% 1.62/0.58  fof(f68,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | v3_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f36])).
% 1.62/0.58  fof(f36,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (v3_tops_1(X1,X0) | ~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(flattening,[],[f35])).
% 1.62/0.58  fof(f35,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((v3_tops_1(X1,X0) | (~v4_pre_topc(X1,X0) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f25])).
% 1.62/0.58  fof(f25,axiom,(
% 1.62/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X1,X0) & v2_tops_1(X1,X0)) => v3_tops_1(X1,X0))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_tops_1)).
% 1.62/0.58  fof(f247,plain,(
% 1.62/0.58    spl2_4 | ~spl2_2),
% 1.62/0.58    inference(avatar_split_clause,[],[f246,f105,f200])).
% 1.62/0.58  fof(f246,plain,(
% 1.62/0.58    v2_tops_1(sK1,sK0) | ~spl2_2),
% 1.62/0.58    inference(subsumption_resolution,[],[f245,f113])).
% 1.62/0.58  fof(f113,plain,(
% 1.62/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.62/0.58    inference(resolution,[],[f81,f110])).
% 1.62/0.58  fof(f110,plain,(
% 1.62/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(forward_demodulation,[],[f63,f61])).
% 1.62/0.58  fof(f63,plain,(
% 1.62/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.62/0.58    inference(cnf_transformation,[],[f11])).
% 1.62/0.58  fof(f11,axiom,(
% 1.62/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.62/0.58  fof(f245,plain,(
% 1.62/0.58    ~r1_tarski(sK1,sK1) | v2_tops_1(sK1,sK0) | ~spl2_2),
% 1.62/0.58    inference(forward_demodulation,[],[f244,f106])).
% 1.62/0.58  fof(f106,plain,(
% 1.62/0.58    sK1 = k2_tops_1(sK0,sK1) | ~spl2_2),
% 1.62/0.58    inference(avatar_component_clause,[],[f105])).
% 1.62/0.58  fof(f244,plain,(
% 1.62/0.58    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0)),
% 1.62/0.58    inference(subsumption_resolution,[],[f237,f55])).
% 1.62/0.58  fof(f237,plain,(
% 1.62/0.58    ~r1_tarski(sK1,k2_tops_1(sK0,sK1)) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0)),
% 1.62/0.58    inference(resolution,[],[f72,f56])).
% 1.62/0.58  fof(f72,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,k2_tops_1(X0,X1)) | v2_tops_1(X1,X0) | ~l1_pre_topc(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f52])).
% 1.62/0.58  fof(f52,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | ~r1_tarski(X1,k2_tops_1(X0,X1))) & (r1_tarski(X1,k2_tops_1(X0,X1)) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(nnf_transformation,[],[f38])).
% 1.62/0.58  fof(f38,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f23])).
% 1.62/0.58  fof(f23,axiom,(
% 1.62/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> r1_tarski(X1,k2_tops_1(X0,X1)))))),
% 1.62/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tops_1)).
% 1.62/0.58  fof(f203,plain,(
% 1.62/0.58    spl2_3 | ~spl2_4),
% 1.62/0.58    inference(avatar_split_clause,[],[f194,f200,f196])).
% 1.62/0.58  fof(f194,plain,(
% 1.62/0.58    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 1.62/0.58    inference(subsumption_resolution,[],[f193,f55])).
% 1.62/0.58  fof(f193,plain,(
% 1.62/0.58    ~v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 1.62/0.58    inference(resolution,[],[f69,f56])).
% 1.62/0.58  fof(f69,plain,(
% 1.62/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tops_1(X1,X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~l1_pre_topc(X0)) )),
% 1.62/0.58    inference(cnf_transformation,[],[f51])).
% 1.62/0.58  fof(f51,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : (((v2_tops_1(X1,X0) | k1_xboole_0 != k1_tops_1(X0,X1)) & (k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(nnf_transformation,[],[f37])).
% 1.62/0.58  fof(f37,plain,(
% 1.62/0.58    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.62/0.58    inference(ennf_transformation,[],[f22])).
% 1.62/0.59  % (2646)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.62/0.59  fof(f22,axiom,(
% 1.62/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 1.62/0.59  fof(f109,plain,(
% 1.62/0.59    spl2_1 | spl2_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f58,f105,f101])).
% 1.62/0.59  fof(f58,plain,(
% 1.62/0.59    sK1 = k2_tops_1(sK0,sK1) | v3_tops_1(sK1,sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f50])).
% 1.62/0.59  fof(f108,plain,(
% 1.62/0.59    ~spl2_1 | ~spl2_2),
% 1.62/0.59    inference(avatar_split_clause,[],[f59,f105,f101])).
% 1.62/0.59  fof(f59,plain,(
% 1.62/0.59    sK1 != k2_tops_1(sK0,sK1) | ~v3_tops_1(sK1,sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f50])).
% 1.62/0.59  % SZS output end Proof for theBenchmark
% 1.62/0.59  % (2670)------------------------------
% 1.62/0.59  % (2670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.59  % (2670)Termination reason: Refutation
% 1.62/0.59  
% 1.62/0.59  % (2670)Memory used [KB]: 6396
% 1.62/0.59  % (2670)Time elapsed: 0.155 s
% 1.62/0.59  % (2670)------------------------------
% 1.62/0.59  % (2670)------------------------------
% 1.62/0.59  % (2642)Success in time 0.225 s
%------------------------------------------------------------------------------
