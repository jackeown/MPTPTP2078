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
% DateTime   : Thu Dec  3 12:46:26 EST 2020

% Result     : Theorem 1.33s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 176 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :   11
%              Number of atoms          :  209 ( 414 expanded)
%              Number of equality atoms :   77 ( 194 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f394,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f345,f355,f372,f376,f387,f390,f393])).

fof(f393,plain,
    ( spl2_2
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | spl2_2
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f384,f70])).

fof(f70,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_2
  <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f384,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f382,f364])).

fof(f364,plain,
    ( m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl2_15
  <=> m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f382,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | ~ m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f38,f380])).

fof(f380,plain,
    ( k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f379,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,k2_subset_1(sK0),k6_setfam_1(sK0,sK1))
    & k1_xboole_0 != sK1
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
        & k1_xboole_0 != X1
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,k2_subset_1(sK0),k6_setfam_1(sK0,sK1))
      & k1_xboole_0 != sK1
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))
      & k1_xboole_0 != X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_xboole_0 != X1
         => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_setfam_1)).

fof(f379,plain,
    ( k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_16 ),
    inference(superposition,[],[f369,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f369,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl2_16
  <=> k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

% (3958)Refutation not found, incomplete strategy% (3958)------------------------------
% (3958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3958)Termination reason: Refutation not found, incomplete strategy

% (3958)Memory used [KB]: 10618
% (3958)Time elapsed: 0.128 s
% (3958)------------------------------
% (3958)------------------------------
fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f390,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f389,f68,f64])).

fof(f64,plain,
    ( spl2_1
  <=> m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f389,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | ~ m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(subsumption_resolution,[],[f358,f47])).

fof(f47,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f34,f33])).

fof(f33,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f34,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f358,plain,
    ( k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f48,f55])).

fof(f55,plain,(
    ! [X6,X4,X5] :
      ( k3_subset_1(X4,X5) = k7_subset_1(X6,X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X6))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X4)) ) ),
    inference(superposition,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f37,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f44,f35])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f48,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,sK0,k6_setfam_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f32,f33])).

fof(f32,plain,(
    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,k2_subset_1(sK0),k6_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f387,plain,
    ( spl2_1
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f386])).

fof(f386,plain,
    ( $false
    | spl2_1
    | ~ spl2_15
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f385,f364])).

fof(f385,plain,
    ( ~ m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | spl2_1
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f383,f66])).

fof(f66,plain,
    ( ~ m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f383,plain,
    ( m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f36,f380])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f376,plain,(
    spl2_15 ),
    inference(avatar_contradiction_clause,[],[f375])).

fof(f375,plain,
    ( $false
    | spl2_15 ),
    inference(subsumption_resolution,[],[f374,f30])).

fof(f374,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl2_15 ),
    inference(resolution,[],[f373,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f373,plain,
    ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl2_15 ),
    inference(resolution,[],[f365,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

fof(f365,plain,
    ( ~ m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f363])).

fof(f372,plain,
    ( ~ spl2_15
    | spl2_16
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f371,f342,f367,f363])).

fof(f342,plain,
    ( spl2_14
  <=> k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k7_subset_1(sK0,sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f371,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f360,f47])).

fof(f360,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
    | ~ spl2_14 ),
    inference(superposition,[],[f55,f344])).

fof(f344,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k7_subset_1(sK0,sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f342])).

fof(f355,plain,(
    ~ spl2_13 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f353,f30])).

fof(f353,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_13 ),
    inference(subsumption_resolution,[],[f352,f31])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f29])).

fof(f352,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_13 ),
    inference(trivial_inequality_removal,[],[f349])).

fof(f349,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl2_13 ),
    inference(superposition,[],[f43,f340])).

fof(f340,plain,
    ( k1_xboole_0 = k7_setfam_1(sK0,sK1)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f338])).

fof(f338,plain,
    ( spl2_13
  <=> k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_xboole_0
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ~ ( k7_setfam_1(X0,X1) = k1_xboole_0
          & k1_xboole_0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

fof(f345,plain,
    ( spl2_13
    | spl2_14 ),
    inference(avatar_split_clause,[],[f335,f342,f338])).

fof(f335,plain,
    ( k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k7_subset_1(sK0,sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))
    | k1_xboole_0 = k7_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f137,f30])).

fof(f137,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5)))
      | k6_setfam_1(X5,k7_setfam_1(X5,k7_setfam_1(X5,X6))) = k7_subset_1(X5,X5,k5_setfam_1(X5,k7_setfam_1(X5,X6)))
      | k1_xboole_0 = k7_setfam_1(X5,X6) ) ),
    inference(resolution,[],[f95,f41])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k5_setfam_1(X0,X1)) ) ),
    inference(forward_demodulation,[],[f42,f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_xboole_0 != X1
       => k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (3937)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (3945)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (3938)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.52  % (3953)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.21/0.52  % (3955)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.21/0.53  % (3938)Refutation not found, incomplete strategy% (3938)------------------------------
% 1.21/0.53  % (3938)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.53  % (3938)Termination reason: Refutation not found, incomplete strategy
% 1.21/0.53  
% 1.21/0.53  % (3938)Memory used [KB]: 10618
% 1.21/0.53  % (3938)Time elapsed: 0.111 s
% 1.21/0.53  % (3938)------------------------------
% 1.21/0.53  % (3938)------------------------------
% 1.33/0.53  % (3939)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.33/0.54  % (3964)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.33/0.54  % (3942)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.33/0.54  % (3953)Refutation not found, incomplete strategy% (3953)------------------------------
% 1.33/0.54  % (3953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (3953)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.54  
% 1.33/0.54  % (3953)Memory used [KB]: 10618
% 1.33/0.54  % (3953)Time elapsed: 0.125 s
% 1.33/0.54  % (3953)------------------------------
% 1.33/0.54  % (3953)------------------------------
% 1.33/0.54  % (3946)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.33/0.54  % (3946)Refutation not found, incomplete strategy% (3946)------------------------------
% 1.33/0.54  % (3946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.54  % (3947)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.33/0.54  % (3944)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.33/0.55  % (3940)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.33/0.55  % (3943)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.33/0.55  % (3946)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.55  
% 1.33/0.55  % (3946)Memory used [KB]: 10618
% 1.33/0.55  % (3946)Time elapsed: 0.123 s
% 1.33/0.55  % (3946)------------------------------
% 1.33/0.55  % (3946)------------------------------
% 1.33/0.55  % (3944)Refutation not found, incomplete strategy% (3944)------------------------------
% 1.33/0.55  % (3944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.55  % (3952)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.33/0.56  % (3936)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.33/0.56  % (3944)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.56  
% 1.33/0.56  % (3944)Memory used [KB]: 10618
% 1.33/0.56  % (3944)Time elapsed: 0.122 s
% 1.33/0.56  % (3944)------------------------------
% 1.33/0.56  % (3944)------------------------------
% 1.33/0.56  % (3963)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.33/0.56  % (3949)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.33/0.56  % (3961)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.33/0.56  % (3956)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.33/0.56  % (3957)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.33/0.56  % (3957)Refutation not found, incomplete strategy% (3957)------------------------------
% 1.33/0.56  % (3957)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.56  % (3957)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.56  
% 1.33/0.56  % (3957)Memory used [KB]: 1663
% 1.33/0.56  % (3957)Time elapsed: 0.159 s
% 1.33/0.56  % (3957)------------------------------
% 1.33/0.56  % (3957)------------------------------
% 1.33/0.56  % (3965)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.33/0.57  % (3948)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.33/0.57  % (3939)Refutation found. Thanks to Tanya!
% 1.33/0.57  % SZS status Theorem for theBenchmark
% 1.33/0.57  % (3958)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.33/0.57  % (3951)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.33/0.57  % SZS output start Proof for theBenchmark
% 1.33/0.57  fof(f394,plain,(
% 1.33/0.57    $false),
% 1.33/0.57    inference(avatar_sat_refutation,[],[f345,f355,f372,f376,f387,f390,f393])).
% 1.33/0.57  fof(f393,plain,(
% 1.33/0.57    spl2_2 | ~spl2_15 | ~spl2_16),
% 1.33/0.57    inference(avatar_contradiction_clause,[],[f392])).
% 1.33/0.57  fof(f392,plain,(
% 1.33/0.57    $false | (spl2_2 | ~spl2_15 | ~spl2_16)),
% 1.33/0.57    inference(subsumption_resolution,[],[f384,f70])).
% 1.33/0.57  fof(f70,plain,(
% 1.33/0.57    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) | spl2_2),
% 1.33/0.57    inference(avatar_component_clause,[],[f68])).
% 1.33/0.57  fof(f68,plain,(
% 1.33/0.57    spl2_2 <=> k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1))),
% 1.33/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.33/0.57  fof(f384,plain,(
% 1.33/0.57    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) | (~spl2_15 | ~spl2_16)),
% 1.33/0.57    inference(subsumption_resolution,[],[f382,f364])).
% 1.33/0.57  fof(f364,plain,(
% 1.33/0.57    m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl2_15),
% 1.33/0.57    inference(avatar_component_clause,[],[f363])).
% 1.33/0.57  fof(f363,plain,(
% 1.33/0.57    spl2_15 <=> m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))),
% 1.33/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 1.33/0.57  fof(f382,plain,(
% 1.33/0.57    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) | ~m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl2_16),
% 1.33/0.57    inference(superposition,[],[f38,f380])).
% 1.33/0.57  fof(f380,plain,(
% 1.33/0.57    k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | ~spl2_16),
% 1.33/0.57    inference(subsumption_resolution,[],[f379,f30])).
% 1.33/0.57  fof(f30,plain,(
% 1.33/0.57    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.33/0.57    inference(cnf_transformation,[],[f29])).
% 1.33/0.57  fof(f29,plain,(
% 1.33/0.57    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,k2_subset_1(sK0),k6_setfam_1(sK0,sK1)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.33/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f28])).
% 1.33/0.57  fof(f28,plain,(
% 1.33/0.57    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,k2_subset_1(sK0),k6_setfam_1(sK0,sK1)) & k1_xboole_0 != sK1 & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.33/0.57    introduced(choice_axiom,[])).
% 1.33/0.57  fof(f16,plain,(
% 1.33/0.57    ? [X0,X1] : (k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) & k1_xboole_0 != X1 & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.57    inference(flattening,[],[f15])).
% 1.33/0.57  fof(f15,plain,(
% 1.33/0.57    ? [X0,X1] : ((k5_setfam_1(X0,k7_setfam_1(X0,X1)) != k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1)) & k1_xboole_0 != X1) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.57    inference(ennf_transformation,[],[f14])).
% 1.33/0.57  fof(f14,negated_conjecture,(
% 1.33/0.57    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))))),
% 1.33/0.57    inference(negated_conjecture,[],[f13])).
% 1.33/0.57  fof(f13,conjecture,(
% 1.33/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k5_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,k2_subset_1(X0),k6_setfam_1(X0,X1))))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_setfam_1)).
% 1.33/0.57  fof(f379,plain,(
% 1.33/0.57    k6_setfam_1(sK0,sK1) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_16),
% 1.33/0.57    inference(superposition,[],[f369,f40])).
% 1.33/0.57  fof(f40,plain,(
% 1.33/0.57    ( ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.33/0.57    inference(cnf_transformation,[],[f21])).
% 1.33/0.57  fof(f21,plain,(
% 1.33/0.57    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.57    inference(ennf_transformation,[],[f10])).
% 1.33/0.57  fof(f10,axiom,(
% 1.33/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 1.33/0.57  fof(f369,plain,(
% 1.33/0.57    k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | ~spl2_16),
% 1.33/0.57    inference(avatar_component_clause,[],[f367])).
% 1.33/0.57  fof(f367,plain,(
% 1.33/0.57    spl2_16 <=> k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))),
% 1.33/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.33/0.57  fof(f38,plain,(
% 1.33/0.57    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.33/0.57    inference(cnf_transformation,[],[f19])).
% 1.33/0.57  fof(f19,plain,(
% 1.33/0.57    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.57    inference(ennf_transformation,[],[f6])).
% 1.33/0.57  % (3958)Refutation not found, incomplete strategy% (3958)------------------------------
% 1.33/0.57  % (3958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.57  % (3958)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.57  
% 1.33/0.57  % (3958)Memory used [KB]: 10618
% 1.33/0.57  % (3958)Time elapsed: 0.128 s
% 1.33/0.57  % (3958)------------------------------
% 1.33/0.57  % (3958)------------------------------
% 1.33/0.57  fof(f6,axiom,(
% 1.33/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.33/0.57  fof(f390,plain,(
% 1.33/0.57    ~spl2_1 | ~spl2_2),
% 1.33/0.57    inference(avatar_split_clause,[],[f389,f68,f64])).
% 1.33/0.57  fof(f64,plain,(
% 1.33/0.57    spl2_1 <=> m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.33/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.33/0.57  fof(f389,plain,(
% 1.33/0.57    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) | ~m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.33/0.57    inference(subsumption_resolution,[],[f358,f47])).
% 1.33/0.57  fof(f47,plain,(
% 1.33/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.33/0.57    inference(forward_demodulation,[],[f34,f33])).
% 1.33/0.57  fof(f33,plain,(
% 1.33/0.57    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.33/0.57    inference(cnf_transformation,[],[f2])).
% 1.33/0.57  fof(f2,axiom,(
% 1.33/0.57    ! [X0] : k2_subset_1(X0) = X0),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.33/0.57  fof(f34,plain,(
% 1.33/0.57    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.33/0.57    inference(cnf_transformation,[],[f4])).
% 1.33/0.57  fof(f4,axiom,(
% 1.33/0.57    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.33/0.57  fof(f358,plain,(
% 1.33/0.57    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k3_subset_1(sK0,k6_setfam_1(sK0,sK1)) | ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.33/0.57    inference(superposition,[],[f48,f55])).
% 1.33/0.57  fof(f55,plain,(
% 1.33/0.57    ( ! [X6,X4,X5] : (k3_subset_1(X4,X5) = k7_subset_1(X6,X4,X5) | ~m1_subset_1(X4,k1_zfmisc_1(X6)) | ~m1_subset_1(X5,k1_zfmisc_1(X4))) )),
% 1.33/0.57    inference(superposition,[],[f46,f45])).
% 1.33/0.57  fof(f45,plain,(
% 1.33/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.33/0.57    inference(definition_unfolding,[],[f37,f35])).
% 1.33/0.57  fof(f35,plain,(
% 1.33/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.33/0.57    inference(cnf_transformation,[],[f1])).
% 1.33/0.57  fof(f1,axiom,(
% 1.33/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.33/0.57  fof(f37,plain,(
% 1.33/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.33/0.57    inference(cnf_transformation,[],[f18])).
% 1.33/0.57  fof(f18,plain,(
% 1.33/0.57    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.57    inference(ennf_transformation,[],[f3])).
% 1.33/0.57  fof(f3,axiom,(
% 1.33/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.33/0.57  fof(f46,plain,(
% 1.33/0.57    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.33/0.57    inference(definition_unfolding,[],[f44,f35])).
% 1.33/0.57  fof(f44,plain,(
% 1.33/0.57    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.33/0.57    inference(cnf_transformation,[],[f27])).
% 1.33/0.57  fof(f27,plain,(
% 1.33/0.57    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.57    inference(ennf_transformation,[],[f7])).
% 1.33/0.57  fof(f7,axiom,(
% 1.33/0.57    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.33/0.57  fof(f48,plain,(
% 1.33/0.57    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,sK0,k6_setfam_1(sK0,sK1))),
% 1.33/0.57    inference(forward_demodulation,[],[f32,f33])).
% 1.33/0.57  fof(f32,plain,(
% 1.33/0.57    k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)) != k7_subset_1(sK0,k2_subset_1(sK0),k6_setfam_1(sK0,sK1))),
% 1.33/0.57    inference(cnf_transformation,[],[f29])).
% 1.33/0.57  fof(f387,plain,(
% 1.33/0.57    spl2_1 | ~spl2_15 | ~spl2_16),
% 1.33/0.57    inference(avatar_contradiction_clause,[],[f386])).
% 1.33/0.57  fof(f386,plain,(
% 1.33/0.57    $false | (spl2_1 | ~spl2_15 | ~spl2_16)),
% 1.33/0.57    inference(subsumption_resolution,[],[f385,f364])).
% 1.33/0.57  fof(f385,plain,(
% 1.33/0.57    ~m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | (spl2_1 | ~spl2_16)),
% 1.33/0.57    inference(subsumption_resolution,[],[f383,f66])).
% 1.33/0.57  fof(f66,plain,(
% 1.33/0.57    ~m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) | spl2_1),
% 1.33/0.57    inference(avatar_component_clause,[],[f64])).
% 1.33/0.57  fof(f383,plain,(
% 1.33/0.57    m1_subset_1(k6_setfam_1(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl2_16),
% 1.33/0.57    inference(superposition,[],[f36,f380])).
% 1.33/0.57  fof(f36,plain,(
% 1.33/0.57    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.33/0.57    inference(cnf_transformation,[],[f17])).
% 1.33/0.57  fof(f17,plain,(
% 1.33/0.57    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.33/0.57    inference(ennf_transformation,[],[f5])).
% 1.33/0.57  fof(f5,axiom,(
% 1.33/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.33/0.57  fof(f376,plain,(
% 1.33/0.57    spl2_15),
% 1.33/0.57    inference(avatar_contradiction_clause,[],[f375])).
% 1.33/0.57  fof(f375,plain,(
% 1.33/0.57    $false | spl2_15),
% 1.33/0.57    inference(subsumption_resolution,[],[f374,f30])).
% 1.33/0.57  fof(f374,plain,(
% 1.33/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl2_15),
% 1.33/0.57    inference(resolution,[],[f373,f41])).
% 1.33/0.57  fof(f41,plain,(
% 1.33/0.57    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.33/0.57    inference(cnf_transformation,[],[f22])).
% 1.33/0.57  fof(f22,plain,(
% 1.33/0.57    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.57    inference(ennf_transformation,[],[f9])).
% 1.33/0.57  fof(f9,axiom,(
% 1.33/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 1.33/0.57  fof(f373,plain,(
% 1.33/0.57    ~m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl2_15),
% 1.33/0.57    inference(resolution,[],[f365,f39])).
% 1.33/0.57  fof(f39,plain,(
% 1.33/0.57    ( ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.33/0.57    inference(cnf_transformation,[],[f20])).
% 1.33/0.57  fof(f20,plain,(
% 1.33/0.57    ! [X0,X1] : (m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.57    inference(ennf_transformation,[],[f8])).
% 1.33/0.57  fof(f8,axiom,(
% 1.33/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k5_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).
% 1.33/0.57  fof(f365,plain,(
% 1.33/0.57    ~m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | spl2_15),
% 1.33/0.57    inference(avatar_component_clause,[],[f363])).
% 1.33/0.57  fof(f372,plain,(
% 1.33/0.57    ~spl2_15 | spl2_16 | ~spl2_14),
% 1.33/0.57    inference(avatar_split_clause,[],[f371,f342,f367,f363])).
% 1.33/0.57  fof(f342,plain,(
% 1.33/0.57    spl2_14 <=> k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k7_subset_1(sK0,sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)))),
% 1.33/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 1.33/0.57  fof(f371,plain,(
% 1.33/0.57    k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | ~m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl2_14),
% 1.33/0.57    inference(subsumption_resolution,[],[f360,f47])).
% 1.33/0.57  fof(f360,plain,(
% 1.33/0.57    k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k3_subset_1(sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~m1_subset_1(k5_setfam_1(sK0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0)) | ~spl2_14),
% 1.33/0.57    inference(superposition,[],[f55,f344])).
% 1.33/0.57  fof(f344,plain,(
% 1.33/0.57    k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k7_subset_1(sK0,sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | ~spl2_14),
% 1.33/0.57    inference(avatar_component_clause,[],[f342])).
% 1.33/0.57  fof(f355,plain,(
% 1.33/0.57    ~spl2_13),
% 1.33/0.57    inference(avatar_contradiction_clause,[],[f354])).
% 1.33/0.57  fof(f354,plain,(
% 1.33/0.57    $false | ~spl2_13),
% 1.33/0.57    inference(subsumption_resolution,[],[f353,f30])).
% 1.33/0.57  fof(f353,plain,(
% 1.33/0.57    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_13),
% 1.33/0.57    inference(subsumption_resolution,[],[f352,f31])).
% 1.33/0.57  fof(f31,plain,(
% 1.33/0.57    k1_xboole_0 != sK1),
% 1.33/0.57    inference(cnf_transformation,[],[f29])).
% 1.33/0.57  fof(f352,plain,(
% 1.33/0.57    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_13),
% 1.33/0.57    inference(trivial_inequality_removal,[],[f349])).
% 1.33/0.57  fof(f349,plain,(
% 1.33/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl2_13),
% 1.33/0.57    inference(superposition,[],[f43,f340])).
% 1.33/0.57  fof(f340,plain,(
% 1.33/0.57    k1_xboole_0 = k7_setfam_1(sK0,sK1) | ~spl2_13),
% 1.33/0.57    inference(avatar_component_clause,[],[f338])).
% 1.33/0.57  fof(f338,plain,(
% 1.33/0.57    spl2_13 <=> k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 1.33/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 1.33/0.57  fof(f43,plain,(
% 1.33/0.57    ( ! [X0,X1] : (k7_setfam_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.33/0.57    inference(cnf_transformation,[],[f26])).
% 1.33/0.57  fof(f26,plain,(
% 1.33/0.57    ! [X0,X1] : (k7_setfam_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.57    inference(flattening,[],[f25])).
% 1.33/0.57  fof(f25,plain,(
% 1.33/0.57    ! [X0,X1] : ((k7_setfam_1(X0,X1) != k1_xboole_0 | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.57    inference(ennf_transformation,[],[f11])).
% 1.33/0.57  fof(f11,axiom,(
% 1.33/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ~(k7_setfam_1(X0,X1) = k1_xboole_0 & k1_xboole_0 != X1))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).
% 1.33/0.57  fof(f345,plain,(
% 1.33/0.57    spl2_13 | spl2_14),
% 1.33/0.57    inference(avatar_split_clause,[],[f335,f342,f338])).
% 1.33/0.57  fof(f335,plain,(
% 1.33/0.57    k6_setfam_1(sK0,k7_setfam_1(sK0,k7_setfam_1(sK0,sK1))) = k7_subset_1(sK0,sK0,k5_setfam_1(sK0,k7_setfam_1(sK0,sK1))) | k1_xboole_0 = k7_setfam_1(sK0,sK1)),
% 1.33/0.57    inference(resolution,[],[f137,f30])).
% 1.33/0.57  fof(f137,plain,(
% 1.33/0.57    ( ! [X6,X5] : (~m1_subset_1(X6,k1_zfmisc_1(k1_zfmisc_1(X5))) | k6_setfam_1(X5,k7_setfam_1(X5,k7_setfam_1(X5,X6))) = k7_subset_1(X5,X5,k5_setfam_1(X5,k7_setfam_1(X5,X6))) | k1_xboole_0 = k7_setfam_1(X5,X6)) )),
% 1.33/0.57    inference(resolution,[],[f95,f41])).
% 1.33/0.57  fof(f95,plain,(
% 1.33/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k6_setfam_1(X0,k7_setfam_1(X0,X1)) = k7_subset_1(X0,X0,k5_setfam_1(X0,X1))) )),
% 1.33/0.57    inference(forward_demodulation,[],[f42,f33])).
% 1.33/0.57  fof(f42,plain,(
% 1.33/0.57    ( ! [X0,X1] : (k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.33/0.57    inference(cnf_transformation,[],[f24])).
% 1.33/0.57  fof(f24,plain,(
% 1.33/0.57    ! [X0,X1] : (k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.57    inference(flattening,[],[f23])).
% 1.33/0.57  fof(f23,plain,(
% 1.33/0.57    ! [X0,X1] : ((k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1)) | k1_xboole_0 = X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.33/0.57    inference(ennf_transformation,[],[f12])).
% 1.33/0.57  fof(f12,axiom,(
% 1.33/0.57    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (k1_xboole_0 != X1 => k7_subset_1(X0,k2_subset_1(X0),k5_setfam_1(X0,X1)) = k6_setfam_1(X0,k7_setfam_1(X0,X1))))),
% 1.33/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_setfam_1)).
% 1.33/0.57  % SZS output end Proof for theBenchmark
% 1.33/0.57  % (3939)------------------------------
% 1.33/0.57  % (3939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.58  % (3941)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.33/0.58  % (3939)Termination reason: Refutation
% 1.33/0.58  
% 1.33/0.58  % (3939)Memory used [KB]: 11001
% 1.33/0.58  % (3939)Time elapsed: 0.159 s
% 1.33/0.58  % (3939)------------------------------
% 1.33/0.58  % (3939)------------------------------
% 1.33/0.58  % (3950)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.33/0.58  % (3935)Success in time 0.213 s
%------------------------------------------------------------------------------
