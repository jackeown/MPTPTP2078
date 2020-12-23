%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:41 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 242 expanded)
%              Number of leaves         :   28 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  309 ( 712 expanded)
%              Number of equality atoms :   55 ( 124 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (18190)Refutation not found, incomplete strategy% (18190)------------------------------
% (18190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18190)Termination reason: Refutation not found, incomplete strategy

% (18190)Memory used [KB]: 10746
% (18190)Time elapsed: 0.114 s
% (18190)------------------------------
% (18190)------------------------------
fof(f437,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f121,f124,f146,f150,f180,f276,f284,f285,f311,f319,f380,f418,f436])).

fof(f436,plain,(
    ~ spl4_22 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | ~ spl4_22 ),
    inference(resolution,[],[f376,f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f376,plain,
    ( ! [X4,X5] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k5_xboole_0(X4,k4_xboole_0(X5,X4))))
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl4_22
  <=> ! [X5,X4] : ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k5_xboole_0(X4,k4_xboole_0(X5,X4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f418,plain,
    ( spl4_4
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(avatar_contradiction_clause,[],[f417])).

fof(f417,plain,
    ( $false
    | spl4_4
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(trivial_inequality_removal,[],[f416])).

fof(f416,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl4_4
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(superposition,[],[f97,f399])).

fof(f399,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_6
    | ~ spl4_23 ),
    inference(resolution,[],[f396,f324])).

fof(f324,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl4_6 ),
    inference(forward_demodulation,[],[f37,f107])).

fof(f107,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl4_6
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f37,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f30,f29])).

fof(f29,plain,
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

fof(f30,plain,
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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f396,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_xboole_0)
        | k1_xboole_0 = X1 )
    | ~ spl4_23 ),
    inference(resolution,[],[f379,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f379,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X3 )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f378])).

fof(f378,plain,
    ( spl4_23
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f97,plain,
    ( k1_xboole_0 != sK1
    | spl4_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f380,plain,
    ( spl4_22
    | spl4_23 ),
    inference(avatar_split_clause,[],[f370,f378,f375])).

fof(f370,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | k1_xboole_0 = X3
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k5_xboole_0(X4,k4_xboole_0(X5,X4)))) ) ),
    inference(resolution,[],[f69,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f41,f54])).

fof(f54,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

% (18214)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f69,plain,(
    ! [X2,X3,X1] :
      ( ~ r1_xboole_0(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X3)) ) ),
    inference(resolution,[],[f67,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f58,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

% (18218)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X1,X3)
      | ~ r1_xboole_0(X1,X3) ) ),
    inference(resolution,[],[f53,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f319,plain,(
    spl4_16 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl4_16 ),
    inference(resolution,[],[f313,f39])).

fof(f313,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_16 ),
    inference(resolution,[],[f312,f65])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f47,f55])).

fof(f55,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f312,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl4_16 ),
    inference(resolution,[],[f310,f50])).

fof(f310,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl4_16
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f311,plain,
    ( ~ spl4_10
    | ~ spl4_16
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f306,f105,f96,f308,f163])).

fof(f163,plain,
    ( spl4_10
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f306,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(superposition,[],[f290,f55])).

fof(f290,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(backward_demodulation,[],[f193,f107])).

fof(f193,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f38,f98])).

fof(f98,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f96])).

fof(f38,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f285,plain,
    ( spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f258,f105,f101])).

fof(f101,plain,
    ( spl4_5
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f258,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(resolution,[],[f36,f82])).

fof(f82,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f48,f46])).

% (18188)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f46,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

% (18191)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f284,plain,
    ( ~ spl4_9
    | spl4_13 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | ~ spl4_9
    | spl4_13 ),
    inference(resolution,[],[f277,f145])).

fof(f145,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_9
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f277,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | spl4_13 ),
    inference(resolution,[],[f275,f50])).

fof(f275,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f273])).

fof(f273,plain,
    ( spl4_13
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f276,plain,
    ( ~ spl4_10
    | ~ spl4_13
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f260,f101,f96,f273,f163])).

fof(f260,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(superposition,[],[f231,f55])).

fof(f231,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f111,f98])).

fof(f111,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f38,f103])).

fof(f103,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f101])).

fof(f180,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f177])).

fof(f177,plain,
    ( $false
    | spl4_10 ),
    inference(resolution,[],[f165,f39])).

fof(f165,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f163])).

fof(f150,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | spl4_8 ),
    inference(resolution,[],[f141,f36])).

fof(f141,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f146,plain,
    ( ~ spl4_8
    | spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f137,f101,f143,f139])).

fof(f137,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl4_5 ),
    inference(superposition,[],[f47,f103])).

fof(f124,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | spl4_7 ),
    inference(resolution,[],[f120,f37])).

fof(f120,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl4_7 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_7
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f121,plain,
    ( ~ spl4_7
    | spl4_4
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f115,f101,f92,f96,f118])).

fof(f92,plain,
    ( spl4_3
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f115,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(resolution,[],[f112,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f112,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f111,f94])).

fof(f94,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f92])).

fof(f99,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f84,f96,f92])).

fof(f84,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(resolution,[],[f82,f35])).

fof(f35,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (18202)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (18193)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (18201)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (18208)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.51  % (18200)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (18201)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (18211)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (18189)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (18190)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (18207)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.52  % (18203)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  % (18190)Refutation not found, incomplete strategy% (18190)------------------------------
% 0.21/0.52  % (18190)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18190)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18190)Memory used [KB]: 10746
% 0.21/0.52  % (18190)Time elapsed: 0.114 s
% 0.21/0.52  % (18190)------------------------------
% 0.21/0.52  % (18190)------------------------------
% 0.21/0.52  fof(f437,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f99,f121,f124,f146,f150,f180,f276,f284,f285,f311,f319,f380,f418,f436])).
% 0.21/0.52  fof(f436,plain,(
% 0.21/0.52    ~spl4_22),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f431])).
% 0.21/0.52  fof(f431,plain,(
% 0.21/0.52    $false | ~spl4_22),
% 0.21/0.52    inference(resolution,[],[f376,f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.52  fof(f376,plain,(
% 0.21/0.52    ( ! [X4,X5] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k5_xboole_0(X4,k4_xboole_0(X5,X4))))) ) | ~spl4_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f375])).
% 0.21/0.52  fof(f375,plain,(
% 0.21/0.52    spl4_22 <=> ! [X5,X4] : ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k5_xboole_0(X4,k4_xboole_0(X5,X4))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.52  fof(f418,plain,(
% 0.21/0.52    spl4_4 | ~spl4_6 | ~spl4_23),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f417])).
% 0.21/0.52  fof(f417,plain,(
% 0.21/0.52    $false | (spl4_4 | ~spl4_6 | ~spl4_23)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f416])).
% 0.21/0.52  fof(f416,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | (spl4_4 | ~spl4_6 | ~spl4_23)),
% 0.21/0.52    inference(superposition,[],[f97,f399])).
% 0.21/0.52  fof(f399,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | (~spl4_6 | ~spl4_23)),
% 0.21/0.52    inference(resolution,[],[f396,f324])).
% 0.21/0.52  fof(f324,plain,(
% 0.21/0.52    r1_tarski(sK1,k1_xboole_0) | ~spl4_6),
% 0.21/0.52    inference(forward_demodulation,[],[f37,f107])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl4_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f105])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl4_6 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f30,f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.52    inference(negated_conjecture,[],[f14])).
% 0.21/0.52  fof(f14,conjecture,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 0.21/0.52  fof(f396,plain,(
% 0.21/0.52    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) ) | ~spl4_23),
% 0.21/0.52    inference(resolution,[],[f379,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.52    inference(nnf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.52  fof(f379,plain,(
% 0.21/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X3) ) | ~spl4_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f378])).
% 0.21/0.52  fof(f378,plain,(
% 0.21/0.52    spl4_23 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    k1_xboole_0 != sK1 | spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl4_4 <=> k1_xboole_0 = sK1),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f380,plain,(
% 0.21/0.52    spl4_22 | spl4_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f370,f378,f375])).
% 0.21/0.52  fof(f370,plain,(
% 0.21/0.52    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = X3 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k5_xboole_0(X4,k4_xboole_0(X5,X4))))) )),
% 0.21/0.52    inference(resolution,[],[f69,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(k1_xboole_0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.52    inference(superposition,[],[f41,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f42,f43])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  % (18214)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X3,X1] : (~r1_xboole_0(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X3))) )),
% 0.21/0.52    inference(resolution,[],[f67,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f34])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_xboole_0(X1,X2) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(resolution,[],[f58,f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK3(X0),X0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  % (18218)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X1,X3) | ~r1_xboole_0(X1,X3)) )),
% 0.21/0.52    inference(resolution,[],[f53,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.21/0.52    inference(flattening,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f12])).
% 0.21/0.52  fof(f12,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.52  fof(f319,plain,(
% 0.21/0.52    spl4_16),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f316])).
% 0.21/0.52  fof(f316,plain,(
% 0.21/0.52    $false | spl4_16),
% 0.21/0.52    inference(resolution,[],[f313,f39])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_16),
% 0.21/0.52    inference(resolution,[],[f312,f65])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f64])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(superposition,[],[f47,f55])).
% 0.21/0.52  fof(f55,plain,(
% 0.21/0.52    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(equality_resolution,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl4_16),
% 0.21/0.52    inference(resolution,[],[f310,f50])).
% 0.21/0.52  fof(f310,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK0) | spl4_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f308])).
% 0.21/0.52  fof(f308,plain,(
% 0.21/0.52    spl4_16 <=> r1_tarski(sK0,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.52  fof(f311,plain,(
% 0.21/0.52    ~spl4_10 | ~spl4_16 | ~spl4_4 | ~spl4_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f306,f105,f96,f308,f163])).
% 0.21/0.52  fof(f163,plain,(
% 0.21/0.52    spl4_10 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f306,plain,(
% 0.21/0.52    ~r1_tarski(sK0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl4_4 | ~spl4_6)),
% 0.21/0.52    inference(superposition,[],[f290,f55])).
% 0.21/0.52  fof(f290,plain,(
% 0.21/0.52    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | (~spl4_4 | ~spl4_6)),
% 0.21/0.52    inference(backward_demodulation,[],[f193,f107])).
% 0.21/0.52  fof(f193,plain,(
% 0.21/0.52    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | ~spl4_4),
% 0.21/0.52    inference(forward_demodulation,[],[f38,f98])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f285,plain,(
% 0.21/0.52    spl4_5 | spl4_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f258,f105,f101])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl4_5 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f258,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 0.21/0.52    inference(resolution,[],[f36,f82])).
% 0.21/0.52  fof(f82,plain,(
% 0.21/0.52    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f79])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 0.21/0.52    inference(superposition,[],[f48,f46])).
% 0.21/0.52  % (18188)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  % (18191)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    ~spl4_9 | spl4_13),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f281])).
% 0.21/0.52  fof(f281,plain,(
% 0.21/0.52    $false | (~spl4_9 | spl4_13)),
% 0.21/0.52    inference(resolution,[],[f277,f145])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f143])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    spl4_9 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.52  fof(f277,plain,(
% 0.21/0.52    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | spl4_13),
% 0.21/0.52    inference(resolution,[],[f275,f50])).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl4_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f273])).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    spl4_13 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.52  fof(f276,plain,(
% 0.21/0.52    ~spl4_10 | ~spl4_13 | ~spl4_4 | ~spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f260,f101,f96,f273,f163])).
% 0.21/0.52  fof(f260,plain,(
% 0.21/0.52    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl4_4 | ~spl4_5)),
% 0.21/0.52    inference(superposition,[],[f231,f55])).
% 0.21/0.52  fof(f231,plain,(
% 0.21/0.52    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (~spl4_4 | ~spl4_5)),
% 0.21/0.52    inference(forward_demodulation,[],[f111,f98])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | ~spl4_5),
% 0.21/0.52    inference(backward_demodulation,[],[f38,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f101])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    spl4_10),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f177])).
% 0.21/0.52  fof(f177,plain,(
% 0.21/0.52    $false | spl4_10),
% 0.21/0.52    inference(resolution,[],[f165,f39])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f163])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    spl4_8),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f147])).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    $false | spl4_8),
% 0.21/0.52    inference(resolution,[],[f141,f36])).
% 0.21/0.52  fof(f141,plain,(
% 0.21/0.52    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl4_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    spl4_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    ~spl4_8 | spl4_9 | ~spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f137,f101,f143,f139])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl4_5),
% 0.21/0.52    inference(superposition,[],[f47,f103])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl4_7),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    $false | spl4_7),
% 0.21/0.52    inference(resolution,[],[f120,f37])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    ~r1_tarski(sK1,sK2) | spl4_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f118])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl4_7 <=> r1_tarski(sK1,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.52  fof(f121,plain,(
% 0.21/0.52    ~spl4_7 | spl4_4 | ~spl4_3 | ~spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f115,f101,f92,f96,f118])).
% 0.21/0.52  fof(f92,plain,(
% 0.21/0.52    spl4_3 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | (~spl4_3 | ~spl4_5)),
% 0.21/0.52    inference(resolution,[],[f112,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (~spl4_3 | ~spl4_5)),
% 0.21/0.52    inference(backward_demodulation,[],[f111,f94])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f92])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl4_3 | spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f84,f96,f92])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 0.21/0.52    inference(resolution,[],[f82,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f31])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (18201)------------------------------
% 0.21/0.52  % (18201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18201)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (18201)Memory used [KB]: 6396
% 0.21/0.52  % (18201)Time elapsed: 0.112 s
% 0.21/0.52  % (18201)------------------------------
% 0.21/0.52  % (18201)------------------------------
% 0.21/0.52  % (18187)Success in time 0.171 s
%------------------------------------------------------------------------------
