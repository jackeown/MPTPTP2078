%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:39 EST 2020

% Result     : Theorem 1.75s
% Output     : Refutation 1.75s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 303 expanded)
%              Number of leaves         :   20 (  95 expanded)
%              Depth                    :   14
%              Number of atoms          :  253 ( 985 expanded)
%              Number of equality atoms :   58 ( 154 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f196,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f92,f116,f131,f179,f195])).

% (2645)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
fof(f195,plain,
    ( ~ spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f193,f36])).

fof(f36,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f29,f28])).

fof(f28,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
            & r1_tarski(X1,X2)
            & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
        & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
          & r1_tarski(sK1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f193,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl4_1
    | spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f192,f67])).

fof(f67,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f192,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(resolution,[],[f182,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f182,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl4_1
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f180,f181])).

fof(f181,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f87,f82])).

fof(f82,plain,(
    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(resolution,[],[f35,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f35,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f87,plain,
    ( k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl4_3
  <=> k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f180,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1))
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f37,f140])).

fof(f140,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl4_1 ),
    inference(forward_demodulation,[],[f64,f59])).

fof(f59,plain,(
    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(resolution,[],[f34,f44])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f30])).

fof(f64,plain,
    ( k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_1
  <=> k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f37,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f30])).

fof(f179,plain,
    ( spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f178])).

fof(f178,plain,
    ( $false
    | spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f177,f67])).

fof(f177,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(resolution,[],[f176,f38])).

fof(f38,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f176,plain,
    ( ! [X2] : ~ r2_hidden(X2,sK1)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f175,f53])).

fof(f53,plain,(
    ! [X0,X1] : k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X0)))) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

% (2640)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f175,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,sK1)
        | k1_xboole_0 = k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_tarski(X2)))) )
    | ~ spl4_4 ),
    inference(resolution,[],[f164,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1 ) ),
    inference(definition_unfolding,[],[f42,f52])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f164,plain,
    ( ! [X0] :
        ( r1_tarski(k1_tarski(X0),k1_xboole_0)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl4_4 ),
    inference(resolution,[],[f137,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(k1_tarski(X0),X1) ) ),
    inference(unused_predicate_definition_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f137,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | r1_tarski(X0,k1_xboole_0) )
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f56,f91])).

fof(f91,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f56,plain,(
    ! [X0] :
      ( r1_tarski(X0,sK2)
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f36,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f131,plain,
    ( ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f129,f107])).

fof(f107,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f106,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f106,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f105,f70])).

fof(f70,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f34,f68])).

fof(f68,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f105,plain,
    ( m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_2 ),
    inference(superposition,[],[f45,f97])).

fof(f97,plain,
    ( sK0 = k8_setfam_1(sK0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(resolution,[],[f70,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k8_setfam_1(X0,k1_xboole_0) = X0 ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f129,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f128,f97])).

fof(f128,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(backward_demodulation,[],[f117,f91])).

fof(f117,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),sK0)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f72,f97])).

fof(f72,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f37,f68])).

fof(f116,plain,
    ( ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f114,f101])).

fof(f101,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f94,f97])).

fof(f94,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f72,f93])).

fof(f93,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f87,f82])).

fof(f114,plain,
    ( r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f113,f48])).

fof(f113,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f112,f35])).

fof(f112,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_3 ),
    inference(superposition,[],[f45,f93])).

fof(f92,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f81,f89,f85])).

fof(f81,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) ),
    inference(resolution,[],[f35,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k1_xboole_0 = X1
      | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f69,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f58,f66,f62])).

fof(f58,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) ),
    inference(resolution,[],[f34,f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 18:35:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.54  % (2633)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.53/0.55  % (2631)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.53/0.56  % (2628)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.53/0.57  % (2634)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.53/0.57  % (2641)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.53/0.57  % (2647)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.53/0.57  % (2629)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.75/0.57  % (2651)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.75/0.58  % (2636)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.75/0.58  % (2637)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.75/0.58  % (2639)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.75/0.58  % (2649)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.75/0.59  % (2632)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.75/0.59  % (2657)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.75/0.59  % (2644)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.75/0.59  % (2638)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.75/0.60  % (2650)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.75/0.60  % (2643)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.75/0.60  % (2636)Refutation found. Thanks to Tanya!
% 1.75/0.60  % SZS status Theorem for theBenchmark
% 1.75/0.60  % (2630)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.75/0.61  % (2642)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.75/0.61  % SZS output start Proof for theBenchmark
% 1.75/0.61  fof(f196,plain,(
% 1.75/0.61    $false),
% 1.75/0.61    inference(avatar_sat_refutation,[],[f69,f92,f116,f131,f179,f195])).
% 1.75/0.61  % (2645)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.75/0.61  fof(f195,plain,(
% 1.75/0.61    ~spl4_1 | spl4_2 | ~spl4_3),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f194])).
% 1.75/0.61  fof(f194,plain,(
% 1.75/0.61    $false | (~spl4_1 | spl4_2 | ~spl4_3)),
% 1.75/0.61    inference(subsumption_resolution,[],[f193,f36])).
% 1.75/0.61  fof(f36,plain,(
% 1.75/0.61    r1_tarski(sK1,sK2)),
% 1.75/0.61    inference(cnf_transformation,[],[f30])).
% 1.75/0.61  fof(f30,plain,(
% 1.75/0.61    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.75/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f29,f28])).
% 1.75/0.61  fof(f28,plain,(
% 1.75/0.61    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.75/0.61    introduced(choice_axiom,[])).
% 1.75/0.61  fof(f29,plain,(
% 1.75/0.61    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.75/0.61    introduced(choice_axiom,[])).
% 1.75/0.61  fof(f17,plain,(
% 1.75/0.61    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.75/0.61    inference(flattening,[],[f16])).
% 1.75/0.61  fof(f16,plain,(
% 1.75/0.61    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.75/0.61    inference(ennf_transformation,[],[f14])).
% 1.75/0.61  fof(f14,negated_conjecture,(
% 1.75/0.61    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.75/0.61    inference(negated_conjecture,[],[f13])).
% 1.75/0.61  fof(f13,conjecture,(
% 1.75/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).
% 1.75/0.61  fof(f193,plain,(
% 1.75/0.61    ~r1_tarski(sK1,sK2) | (~spl4_1 | spl4_2 | ~spl4_3)),
% 1.75/0.61    inference(subsumption_resolution,[],[f192,f67])).
% 1.75/0.61  fof(f67,plain,(
% 1.75/0.61    k1_xboole_0 != sK1 | spl4_2),
% 1.75/0.61    inference(avatar_component_clause,[],[f66])).
% 1.75/0.61  fof(f66,plain,(
% 1.75/0.61    spl4_2 <=> k1_xboole_0 = sK1),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.75/0.61  fof(f192,plain,(
% 1.75/0.61    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | (~spl4_1 | ~spl4_3)),
% 1.75/0.61    inference(resolution,[],[f182,f43])).
% 1.75/0.61  fof(f43,plain,(
% 1.75/0.61    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f21])).
% 1.75/0.61  fof(f21,plain,(
% 1.75/0.61    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.75/0.61    inference(flattening,[],[f20])).
% 1.75/0.61  fof(f20,plain,(
% 1.75/0.61    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.75/0.61    inference(ennf_transformation,[],[f12])).
% 1.75/0.61  fof(f12,axiom,(
% 1.75/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.75/0.61  fof(f182,plain,(
% 1.75/0.61    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (~spl4_1 | ~spl4_3)),
% 1.75/0.61    inference(backward_demodulation,[],[f180,f181])).
% 1.75/0.61  fof(f181,plain,(
% 1.75/0.61    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl4_3),
% 1.75/0.61    inference(forward_demodulation,[],[f87,f82])).
% 1.75/0.61  fof(f82,plain,(
% 1.75/0.61    k6_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.75/0.61    inference(resolution,[],[f35,f44])).
% 1.75/0.61  fof(f44,plain,(
% 1.75/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k6_setfam_1(X0,X1) = k1_setfam_1(X1)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f22])).
% 1.75/0.61  fof(f22,plain,(
% 1.75/0.61    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.75/0.61    inference(ennf_transformation,[],[f10])).
% 1.75/0.61  fof(f10,axiom,(
% 1.75/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 1.75/0.61  fof(f35,plain,(
% 1.75/0.61    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.75/0.61    inference(cnf_transformation,[],[f30])).
% 1.75/0.61  fof(f87,plain,(
% 1.75/0.61    k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2) | ~spl4_3),
% 1.75/0.61    inference(avatar_component_clause,[],[f85])).
% 1.75/0.61  fof(f85,plain,(
% 1.75/0.61    spl4_3 <=> k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.75/0.61  fof(f180,plain,(
% 1.75/0.61    ~r1_tarski(k8_setfam_1(sK0,sK2),k1_setfam_1(sK1)) | ~spl4_1),
% 1.75/0.61    inference(forward_demodulation,[],[f37,f140])).
% 1.75/0.61  fof(f140,plain,(
% 1.75/0.61    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl4_1),
% 1.75/0.61    inference(forward_demodulation,[],[f64,f59])).
% 1.75/0.61  fof(f59,plain,(
% 1.75/0.61    k6_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 1.75/0.61    inference(resolution,[],[f34,f44])).
% 1.75/0.61  fof(f34,plain,(
% 1.75/0.61    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.75/0.61    inference(cnf_transformation,[],[f30])).
% 1.75/0.61  fof(f64,plain,(
% 1.75/0.61    k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1) | ~spl4_1),
% 1.75/0.61    inference(avatar_component_clause,[],[f62])).
% 1.75/0.61  fof(f62,plain,(
% 1.75/0.61    spl4_1 <=> k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.75/0.61  fof(f37,plain,(
% 1.75/0.61    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.75/0.61    inference(cnf_transformation,[],[f30])).
% 1.75/0.61  fof(f179,plain,(
% 1.75/0.61    spl4_2 | ~spl4_4),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f178])).
% 1.75/0.61  fof(f178,plain,(
% 1.75/0.61    $false | (spl4_2 | ~spl4_4)),
% 1.75/0.61    inference(subsumption_resolution,[],[f177,f67])).
% 1.75/0.61  fof(f177,plain,(
% 1.75/0.61    k1_xboole_0 = sK1 | ~spl4_4),
% 1.75/0.61    inference(resolution,[],[f176,f38])).
% 1.75/0.61  fof(f38,plain,(
% 1.75/0.61    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 1.75/0.61    inference(cnf_transformation,[],[f32])).
% 1.75/0.61  fof(f32,plain,(
% 1.75/0.61    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 1.75/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f31])).
% 1.75/0.61  fof(f31,plain,(
% 1.75/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 1.75/0.61    introduced(choice_axiom,[])).
% 1.75/0.61  fof(f18,plain,(
% 1.75/0.61    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.75/0.61    inference(ennf_transformation,[],[f1])).
% 1.75/0.61  fof(f1,axiom,(
% 1.75/0.61    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.75/0.61  fof(f176,plain,(
% 1.75/0.61    ( ! [X2] : (~r2_hidden(X2,sK1)) ) | ~spl4_4),
% 1.75/0.61    inference(subsumption_resolution,[],[f175,f53])).
% 1.75/0.61  fof(f53,plain,(
% 1.75/0.61    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k1_tarski(X0),k5_xboole_0(X1,k3_xboole_0(X1,k1_tarski(X0))))) )),
% 1.75/0.61    inference(definition_unfolding,[],[f39,f52])).
% 1.75/0.61  fof(f52,plain,(
% 1.75/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.75/0.61    inference(definition_unfolding,[],[f41,f40])).
% 1.75/0.61  fof(f40,plain,(
% 1.75/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.75/0.61    inference(cnf_transformation,[],[f2])).
% 1.75/0.61  fof(f2,axiom,(
% 1.75/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.75/0.61  % (2640)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.75/0.61  fof(f41,plain,(
% 1.75/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.75/0.61    inference(cnf_transformation,[],[f5])).
% 1.75/0.61  fof(f5,axiom,(
% 1.75/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.75/0.61  fof(f39,plain,(
% 1.75/0.61    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f7])).
% 1.75/0.61  fof(f7,axiom,(
% 1.75/0.61    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.75/0.61  fof(f175,plain,(
% 1.75/0.61    ( ! [X2] : (~r2_hidden(X2,sK1) | k1_xboole_0 = k5_xboole_0(k1_tarski(X2),k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_tarski(X2))))) ) | ~spl4_4),
% 1.75/0.61    inference(resolution,[],[f164,f54])).
% 1.75/0.61  fof(f54,plain,(
% 1.75/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = X1) )),
% 1.75/0.61    inference(definition_unfolding,[],[f42,f52])).
% 1.75/0.61  fof(f42,plain,(
% 1.75/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f19])).
% 1.75/0.61  fof(f19,plain,(
% 1.75/0.61    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.75/0.61    inference(ennf_transformation,[],[f3])).
% 1.75/0.61  fof(f3,axiom,(
% 1.75/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.75/0.61  fof(f164,plain,(
% 1.75/0.61    ( ! [X0] : (r1_tarski(k1_tarski(X0),k1_xboole_0) | ~r2_hidden(X0,sK1)) ) | ~spl4_4),
% 1.75/0.61    inference(resolution,[],[f137,f50])).
% 1.75/0.61  fof(f50,plain,(
% 1.75/0.61    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f25])).
% 1.75/0.61  fof(f25,plain,(
% 1.75/0.61    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 1.75/0.61    inference(ennf_transformation,[],[f15])).
% 1.75/0.61  fof(f15,plain,(
% 1.75/0.61    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(k1_tarski(X0),X1))),
% 1.75/0.61    inference(unused_predicate_definition_removal,[],[f6])).
% 1.75/0.61  fof(f6,axiom,(
% 1.75/0.61    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.75/0.61  fof(f137,plain,(
% 1.75/0.61    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,k1_xboole_0)) ) | ~spl4_4),
% 1.75/0.61    inference(forward_demodulation,[],[f56,f91])).
% 1.75/0.61  fof(f91,plain,(
% 1.75/0.61    k1_xboole_0 = sK2 | ~spl4_4),
% 1.75/0.61    inference(avatar_component_clause,[],[f89])).
% 1.75/0.61  fof(f89,plain,(
% 1.75/0.61    spl4_4 <=> k1_xboole_0 = sK2),
% 1.75/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.75/0.61  fof(f56,plain,(
% 1.75/0.61    ( ! [X0] : (r1_tarski(X0,sK2) | ~r1_tarski(X0,sK1)) )),
% 1.75/0.61    inference(resolution,[],[f36,f51])).
% 1.75/0.61  fof(f51,plain,(
% 1.75/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f27])).
% 1.75/0.61  fof(f27,plain,(
% 1.75/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.75/0.61    inference(flattening,[],[f26])).
% 1.75/0.61  fof(f26,plain,(
% 1.75/0.61    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.75/0.61    inference(ennf_transformation,[],[f4])).
% 1.75/0.61  fof(f4,axiom,(
% 1.75/0.61    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.75/0.61  fof(f131,plain,(
% 1.75/0.61    ~spl4_2 | ~spl4_4),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f130])).
% 1.75/0.61  fof(f130,plain,(
% 1.75/0.61    $false | (~spl4_2 | ~spl4_4)),
% 1.75/0.61    inference(subsumption_resolution,[],[f129,f107])).
% 1.75/0.61  fof(f107,plain,(
% 1.75/0.61    r1_tarski(sK0,sK0) | ~spl4_2),
% 1.75/0.61    inference(resolution,[],[f106,f48])).
% 1.75/0.61  fof(f48,plain,(
% 1.75/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f33])).
% 1.75/0.61  fof(f33,plain,(
% 1.75/0.61    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.75/0.61    inference(nnf_transformation,[],[f11])).
% 1.75/0.61  fof(f11,axiom,(
% 1.75/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.75/0.61  fof(f106,plain,(
% 1.75/0.61    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~spl4_2),
% 1.75/0.61    inference(subsumption_resolution,[],[f105,f70])).
% 1.75/0.61  fof(f70,plain,(
% 1.75/0.61    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_2),
% 1.75/0.61    inference(backward_demodulation,[],[f34,f68])).
% 1.75/0.61  fof(f68,plain,(
% 1.75/0.61    k1_xboole_0 = sK1 | ~spl4_2),
% 1.75/0.61    inference(avatar_component_clause,[],[f66])).
% 1.75/0.61  fof(f105,plain,(
% 1.75/0.61    m1_subset_1(sK0,k1_zfmisc_1(sK0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_2),
% 1.75/0.61    inference(superposition,[],[f45,f97])).
% 1.75/0.61  fof(f97,plain,(
% 1.75/0.61    sK0 = k8_setfam_1(sK0,k1_xboole_0) | ~spl4_2),
% 1.75/0.61    inference(resolution,[],[f70,f55])).
% 1.75/0.61  fof(f55,plain,(
% 1.75/0.61    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | k8_setfam_1(X0,k1_xboole_0) = X0) )),
% 1.75/0.61    inference(equality_resolution,[],[f47])).
% 1.75/0.61  fof(f47,plain,(
% 1.75/0.61    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.75/0.61    inference(cnf_transformation,[],[f24])).
% 1.75/0.61  fof(f24,plain,(
% 1.75/0.61    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.75/0.61    inference(ennf_transformation,[],[f8])).
% 1.75/0.61  fof(f8,axiom,(
% 1.75/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.75/0.61  fof(f45,plain,(
% 1.75/0.61    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.75/0.61    inference(cnf_transformation,[],[f23])).
% 1.75/0.61  fof(f23,plain,(
% 1.75/0.61    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.75/0.61    inference(ennf_transformation,[],[f9])).
% 1.75/0.61  fof(f9,axiom,(
% 1.75/0.61    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.75/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 1.75/0.61  fof(f129,plain,(
% 1.75/0.61    ~r1_tarski(sK0,sK0) | (~spl4_2 | ~spl4_4)),
% 1.75/0.61    inference(forward_demodulation,[],[f128,f97])).
% 1.75/0.61  fof(f128,plain,(
% 1.75/0.61    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),sK0) | (~spl4_2 | ~spl4_4)),
% 1.75/0.61    inference(backward_demodulation,[],[f117,f91])).
% 1.75/0.61  fof(f117,plain,(
% 1.75/0.61    ~r1_tarski(k8_setfam_1(sK0,sK2),sK0) | ~spl4_2),
% 1.75/0.61    inference(forward_demodulation,[],[f72,f97])).
% 1.75/0.61  fof(f72,plain,(
% 1.75/0.61    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | ~spl4_2),
% 1.75/0.61    inference(backward_demodulation,[],[f37,f68])).
% 1.75/0.61  fof(f116,plain,(
% 1.75/0.61    ~spl4_2 | ~spl4_3),
% 1.75/0.61    inference(avatar_contradiction_clause,[],[f115])).
% 1.75/0.61  fof(f115,plain,(
% 1.75/0.61    $false | (~spl4_2 | ~spl4_3)),
% 1.75/0.61    inference(subsumption_resolution,[],[f114,f101])).
% 1.75/0.61  fof(f101,plain,(
% 1.75/0.61    ~r1_tarski(k1_setfam_1(sK2),sK0) | (~spl4_2 | ~spl4_3)),
% 1.75/0.61    inference(backward_demodulation,[],[f94,f97])).
% 1.75/0.61  fof(f94,plain,(
% 1.75/0.61    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (~spl4_2 | ~spl4_3)),
% 1.75/0.61    inference(backward_demodulation,[],[f72,f93])).
% 1.75/0.61  fof(f93,plain,(
% 1.75/0.61    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl4_3),
% 1.75/0.61    inference(forward_demodulation,[],[f87,f82])).
% 1.75/0.61  fof(f114,plain,(
% 1.75/0.61    r1_tarski(k1_setfam_1(sK2),sK0) | ~spl4_3),
% 1.75/0.61    inference(resolution,[],[f113,f48])).
% 1.75/0.61  fof(f113,plain,(
% 1.75/0.61    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl4_3),
% 1.75/0.61    inference(subsumption_resolution,[],[f112,f35])).
% 1.75/0.61  fof(f112,plain,(
% 1.75/0.61    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_3),
% 1.75/0.61    inference(superposition,[],[f45,f93])).
% 1.75/0.61  fof(f92,plain,(
% 1.75/0.61    spl4_3 | spl4_4),
% 1.75/0.61    inference(avatar_split_clause,[],[f81,f89,f85])).
% 1.75/0.61  fof(f81,plain,(
% 1.75/0.61    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k6_setfam_1(sK0,sK2)),
% 1.75/0.61    inference(resolution,[],[f35,f46])).
% 1.75/0.61  fof(f46,plain,(
% 1.75/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k1_xboole_0 = X1 | k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)) )),
% 1.75/0.61    inference(cnf_transformation,[],[f24])).
% 1.75/0.61  fof(f69,plain,(
% 1.75/0.61    spl4_1 | spl4_2),
% 1.75/0.61    inference(avatar_split_clause,[],[f58,f66,f62])).
% 1.75/0.61  fof(f58,plain,(
% 1.75/0.61    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k6_setfam_1(sK0,sK1)),
% 1.75/0.61    inference(resolution,[],[f34,f46])).
% 1.75/0.61  % SZS output end Proof for theBenchmark
% 1.75/0.61  % (2636)------------------------------
% 1.75/0.61  % (2636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.61  % (2636)Termination reason: Refutation
% 1.75/0.61  
% 1.75/0.61  % (2636)Memory used [KB]: 10746
% 1.75/0.61  % (2636)Time elapsed: 0.192 s
% 1.75/0.61  % (2636)------------------------------
% 1.75/0.61  % (2636)------------------------------
% 1.75/0.61  % (2627)Success in time 0.259 s
%------------------------------------------------------------------------------
