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
% DateTime   : Thu Dec  3 12:46:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 242 expanded)
%              Number of leaves         :   24 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  262 ( 727 expanded)
%              Number of equality atoms :   60 ( 137 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f270,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f131,f145,f149,f172,f175,f196,f218,f223,f242,f249,f269])).

fof(f269,plain,
    ( spl3_6
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | spl3_6
    | ~ spl3_8 ),
    inference(trivial_inequality_removal,[],[f267])).

fof(f267,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f120,f257])).

fof(f257,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_8 ),
    inference(resolution,[],[f253,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f56,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f56,plain,(
    ! [X0] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_xboole_0)
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f47,f46])).

fof(f46,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f30,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f44])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f253,plain,
    ( r1_tarski(sK1,k1_xboole_0)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f28,f130])).

fof(f130,plain,
    ( k1_xboole_0 = sK2
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f128,plain,
    ( spl3_8
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f28,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
    & r1_tarski(sK1,sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f22,f21])).

% (18851)Refutation not found, incomplete strategy% (18851)------------------------------
% (18851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18857)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (18851)Termination reason: Refutation not found, incomplete strategy

% (18851)Memory used [KB]: 10618
% (18851)Time elapsed: 0.120 s
% (18851)------------------------------
% (18851)------------------------------
% (18864)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (18862)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (18864)Refutation not found, incomplete strategy% (18864)------------------------------
% (18864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (18864)Termination reason: Refutation not found, incomplete strategy

% (18864)Memory used [KB]: 10618
% (18864)Time elapsed: 0.102 s
% (18864)------------------------------
% (18864)------------------------------
% (18848)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (18847)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f21,plain,
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

fof(f22,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1))
        & r1_tarski(sK1,X2)
        & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0))) )
   => ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))
      & r1_tarski(sK1,sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1))
          & r1_tarski(X1,X2)
          & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

fof(f120,plain,
    ( k1_xboole_0 != sK1
    | spl3_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_6
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f249,plain,
    ( ~ spl3_6
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f247])).

fof(f247,plain,
    ( $false
    | ~ spl3_6
    | spl3_16 ),
    inference(resolution,[],[f245,f150])).

fof(f150,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f26,f121])).

fof(f121,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f119])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f245,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_16 ),
    inference(resolution,[],[f244,f55])).

fof(f55,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(duplicate_literal_removal,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(superposition,[],[f37,f49])).

fof(f49,plain,(
    ! [X0] :
      ( k8_setfam_1(X0,k1_xboole_0) = X0
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ( k8_setfam_1(X0,X1) = X0
          | k1_xboole_0 != X1 )
        & ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
          | k1_xboole_0 = X1 ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( ( k1_xboole_0 = X1
         => k8_setfam_1(X0,X1) = X0 )
        & ( k1_xboole_0 != X1
         => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

fof(f244,plain,
    ( ~ m1_subset_1(sK0,k1_zfmisc_1(sK0))
    | spl3_16 ),
    inference(resolution,[],[f241,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f241,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl3_16
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f242,plain,
    ( ~ spl3_12
    | ~ spl3_16
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f237,f128,f119,f239,f180])).

fof(f180,plain,
    ( spl3_12
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f237,plain,
    ( ~ r1_tarski(sK0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(superposition,[],[f231,f49])).

fof(f231,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(backward_demodulation,[],[f224,f130])).

fof(f224,plain,
    ( ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f29,f121])).

fof(f29,plain,(
    ~ r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f223,plain,
    ( ~ spl3_11
    | spl3_15 ),
    inference(avatar_contradiction_clause,[],[f221])).

fof(f221,plain,
    ( $false
    | ~ spl3_11
    | spl3_15 ),
    inference(resolution,[],[f220,f171])).

fof(f171,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f169])).

fof(f169,plain,
    ( spl3_11
  <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f220,plain,
    ( ~ m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | spl3_15 ),
    inference(resolution,[],[f217,f40])).

fof(f217,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | spl3_15 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl3_15
  <=> r1_tarski(k1_setfam_1(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f218,plain,
    ( ~ spl3_12
    | ~ spl3_15
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f213,f124,f119,f215,f180])).

fof(f124,plain,
    ( spl3_7
  <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f213,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f209,f49])).

fof(f209,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f134,f121])).

fof(f134,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1))
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f29,f126])).

fof(f126,plain,
    ( k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f124])).

fof(f196,plain,
    ( ~ spl3_6
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl3_6
    | spl3_12 ),
    inference(resolution,[],[f182,f150])).

fof(f182,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f180])).

fof(f175,plain,(
    spl3_10 ),
    inference(avatar_contradiction_clause,[],[f173])).

fof(f173,plain,
    ( $false
    | spl3_10 ),
    inference(resolution,[],[f167,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f167,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl3_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f172,plain,
    ( ~ spl3_10
    | spl3_11
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f163,f124,f169,f165])).

fof(f163,plain,
    ( m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | ~ spl3_7 ),
    inference(superposition,[],[f37,f126])).

fof(f149,plain,(
    spl3_9 ),
    inference(avatar_contradiction_clause,[],[f146])).

fof(f146,plain,
    ( $false
    | spl3_9 ),
    inference(resolution,[],[f144,f28])).

fof(f144,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl3_9
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f145,plain,
    ( ~ spl3_9
    | spl3_6
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f138,f124,f115,f119,f142])).

fof(f115,plain,
    ( spl3_5
  <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f138,plain,
    ( k1_xboole_0 = sK1
    | ~ r1_tarski(sK1,sK2)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f135,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0))
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

fof(f135,plain,
    ( ~ r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1))
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f134,f117])).

fof(f117,plain,
    ( k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f131,plain,
    ( spl3_7
    | spl3_8 ),
    inference(avatar_split_clause,[],[f110,f128,f124])).

fof(f110,plain,
    ( k1_xboole_0 = sK2
    | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) ),
    inference(resolution,[],[f88,f27])).

fof(f88,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | k1_xboole_0 = X3
      | k1_setfam_1(X3) = k8_setfam_1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f85])).

fof(f85,plain,(
    ! [X2,X3] :
      ( k1_setfam_1(X3) = k8_setfam_1(X2,X3)
      | k1_xboole_0 = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) ) ),
    inference(superposition,[],[f38,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_setfam_1(X0,X1) = k1_setfam_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k6_setfam_1(X0,X1) = k1_setfam_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f122,plain,
    ( spl3_5
    | spl3_6 ),
    inference(avatar_split_clause,[],[f109,f119,f115])).

fof(f109,plain,
    ( k1_xboole_0 = sK1
    | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) ),
    inference(resolution,[],[f88,f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:42:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.51  % (18868)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.51  % (18866)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (18854)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (18846)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (18851)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (18843)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (18854)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f270,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f122,f131,f145,f149,f172,f175,f196,f218,f223,f242,f249,f269])).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    spl3_6 | ~spl3_8),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f268])).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    $false | (spl3_6 | ~spl3_8)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f267])).
% 0.21/0.52  fof(f267,plain,(
% 0.21/0.52    k1_xboole_0 != k1_xboole_0 | (spl3_6 | ~spl3_8)),
% 0.21/0.52    inference(superposition,[],[f120,f257])).
% 0.21/0.52  fof(f257,plain,(
% 0.21/0.52    k1_xboole_0 = sK1 | ~spl3_8),
% 0.21/0.52    inference(resolution,[],[f253,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.52    inference(forward_demodulation,[],[f56,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k1_xboole_0) | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(superposition,[],[f47,f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(X0,X0,k1_xboole_0))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f30,f44])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f32,f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1))) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f43,f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k1_enumset1(X0,X0,X1)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f34,f44])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.52    inference(nnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.52  fof(f253,plain,(
% 0.21/0.52    r1_tarski(sK1,k1_xboole_0) | ~spl3_8),
% 0.21/0.52    inference(forward_demodulation,[],[f28,f130])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    k1_xboole_0 = sK2 | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f128])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    spl3_8 <=> k1_xboole_0 = sK2),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    r1_tarski(sK1,sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f22,f21])).
% 0.21/0.52  % (18851)Refutation not found, incomplete strategy% (18851)------------------------------
% 0.21/0.52  % (18851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (18857)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (18851)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (18851)Memory used [KB]: 10618
% 0.21/0.52  % (18851)Time elapsed: 0.120 s
% 0.21/0.52  % (18851)------------------------------
% 0.21/0.52  % (18851)------------------------------
% 0.21/0.52  % (18864)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (18862)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.29/0.53  % (18864)Refutation not found, incomplete strategy% (18864)------------------------------
% 1.29/0.53  % (18864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (18864)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (18864)Memory used [KB]: 10618
% 1.29/0.53  % (18864)Time elapsed: 0.102 s
% 1.29/0.53  % (18864)------------------------------
% 1.29/0.53  % (18864)------------------------------
% 1.29/0.53  % (18848)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.53  % (18847)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.53  fof(f21,plain,(
% 1.29/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) => (? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f22,plain,(
% 1.29/0.53    ? [X2] : (~r1_tarski(k8_setfam_1(sK0,X2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(sK0)))) => (~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1)) & r1_tarski(sK1,sK2) & m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))))),
% 1.29/0.53    introduced(choice_axiom,[])).
% 1.29/0.53  fof(f15,plain,(
% 1.29/0.53    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.29/0.53    inference(flattening,[],[f14])).
% 1.29/0.53  fof(f14,plain,(
% 1.29/0.53    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.29/0.53    inference(ennf_transformation,[],[f13])).
% 1.29/0.53  fof(f13,negated_conjecture,(
% 1.29/0.53    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.29/0.53    inference(negated_conjecture,[],[f12])).
% 1.29/0.53  fof(f12,conjecture,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(X1,X2) => r1_tarski(k8_setfam_1(X0,X2),k8_setfam_1(X0,X1)))))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).
% 1.29/0.53  fof(f120,plain,(
% 1.29/0.53    k1_xboole_0 != sK1 | spl3_6),
% 1.29/0.53    inference(avatar_component_clause,[],[f119])).
% 1.29/0.53  fof(f119,plain,(
% 1.29/0.53    spl3_6 <=> k1_xboole_0 = sK1),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.29/0.53  fof(f249,plain,(
% 1.29/0.53    ~spl3_6 | spl3_16),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f247])).
% 1.29/0.53  fof(f247,plain,(
% 1.29/0.53    $false | (~spl3_6 | spl3_16)),
% 1.29/0.53    inference(resolution,[],[f245,f150])).
% 1.29/0.53  fof(f150,plain,(
% 1.29/0.53    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_6),
% 1.29/0.53    inference(backward_demodulation,[],[f26,f121])).
% 1.29/0.53  fof(f121,plain,(
% 1.29/0.53    k1_xboole_0 = sK1 | ~spl3_6),
% 1.29/0.53    inference(avatar_component_clause,[],[f119])).
% 1.29/0.53  fof(f26,plain,(
% 1.29/0.53    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.29/0.53    inference(cnf_transformation,[],[f23])).
% 1.29/0.53  fof(f245,plain,(
% 1.29/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_16),
% 1.29/0.53    inference(resolution,[],[f244,f55])).
% 1.29/0.53  fof(f55,plain,(
% 1.29/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.29/0.53    inference(duplicate_literal_removal,[],[f54])).
% 1.29/0.53  fof(f54,plain,(
% 1.29/0.53    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.29/0.53    inference(superposition,[],[f37,f49])).
% 1.29/0.53  fof(f49,plain,(
% 1.29/0.53    ( ! [X0] : (k8_setfam_1(X0,k1_xboole_0) = X0 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.29/0.53    inference(equality_resolution,[],[f39])).
% 1.29/0.53  fof(f39,plain,(
% 1.29/0.53    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f20])).
% 1.29/0.53  fof(f20,plain,(
% 1.29/0.53    ! [X0,X1] : (((k8_setfam_1(X0,X1) = X0 | k1_xboole_0 != X1) & (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.29/0.53    inference(ennf_transformation,[],[f6])).
% 1.29/0.53  fof(f6,axiom,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ((k1_xboole_0 = X1 => k8_setfam_1(X0,X1) = X0) & (k1_xboole_0 != X1 => k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1))))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).
% 1.29/0.53  fof(f37,plain,(
% 1.29/0.53    ( ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f19])).
% 1.29/0.53  fof(f19,plain,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.29/0.53    inference(ennf_transformation,[],[f7])).
% 1.29/0.53  fof(f7,axiom,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k8_setfam_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).
% 1.29/0.53  fof(f244,plain,(
% 1.29/0.53    ~m1_subset_1(sK0,k1_zfmisc_1(sK0)) | spl3_16),
% 1.29/0.53    inference(resolution,[],[f241,f40])).
% 1.29/0.53  fof(f40,plain,(
% 1.29/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f24])).
% 1.29/0.53  fof(f24,plain,(
% 1.29/0.53    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.29/0.53    inference(nnf_transformation,[],[f10])).
% 1.29/0.53  fof(f10,axiom,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.29/0.53  fof(f241,plain,(
% 1.29/0.53    ~r1_tarski(sK0,sK0) | spl3_16),
% 1.29/0.53    inference(avatar_component_clause,[],[f239])).
% 1.29/0.53  fof(f239,plain,(
% 1.29/0.53    spl3_16 <=> r1_tarski(sK0,sK0)),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.29/0.53  fof(f242,plain,(
% 1.29/0.53    ~spl3_12 | ~spl3_16 | ~spl3_6 | ~spl3_8),
% 1.29/0.53    inference(avatar_split_clause,[],[f237,f128,f119,f239,f180])).
% 1.29/0.53  fof(f180,plain,(
% 1.29/0.53    spl3_12 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.29/0.53  fof(f237,plain,(
% 1.29/0.53    ~r1_tarski(sK0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_6 | ~spl3_8)),
% 1.29/0.53    inference(superposition,[],[f231,f49])).
% 1.29/0.53  fof(f231,plain,(
% 1.29/0.53    ~r1_tarski(k8_setfam_1(sK0,k1_xboole_0),k8_setfam_1(sK0,k1_xboole_0)) | (~spl3_6 | ~spl3_8)),
% 1.29/0.53    inference(backward_demodulation,[],[f224,f130])).
% 1.29/0.53  fof(f224,plain,(
% 1.29/0.53    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,k1_xboole_0)) | ~spl3_6),
% 1.29/0.53    inference(forward_demodulation,[],[f29,f121])).
% 1.29/0.53  fof(f29,plain,(
% 1.29/0.53    ~r1_tarski(k8_setfam_1(sK0,sK2),k8_setfam_1(sK0,sK1))),
% 1.29/0.53    inference(cnf_transformation,[],[f23])).
% 1.29/0.53  fof(f223,plain,(
% 1.29/0.53    ~spl3_11 | spl3_15),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f221])).
% 1.29/0.53  fof(f221,plain,(
% 1.29/0.53    $false | (~spl3_11 | spl3_15)),
% 1.29/0.53    inference(resolution,[],[f220,f171])).
% 1.29/0.53  fof(f171,plain,(
% 1.29/0.53    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~spl3_11),
% 1.29/0.53    inference(avatar_component_clause,[],[f169])).
% 1.29/0.53  fof(f169,plain,(
% 1.29/0.53    spl3_11 <=> m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0))),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.29/0.53  fof(f220,plain,(
% 1.29/0.53    ~m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | spl3_15),
% 1.29/0.53    inference(resolution,[],[f217,f40])).
% 1.29/0.53  fof(f217,plain,(
% 1.29/0.53    ~r1_tarski(k1_setfam_1(sK2),sK0) | spl3_15),
% 1.29/0.53    inference(avatar_component_clause,[],[f215])).
% 1.29/0.53  fof(f215,plain,(
% 1.29/0.53    spl3_15 <=> r1_tarski(k1_setfam_1(sK2),sK0)),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.29/0.53  fof(f218,plain,(
% 1.29/0.53    ~spl3_12 | ~spl3_15 | ~spl3_6 | ~spl3_7),
% 1.29/0.53    inference(avatar_split_clause,[],[f213,f124,f119,f215,f180])).
% 1.29/0.53  fof(f124,plain,(
% 1.29/0.53    spl3_7 <=> k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.29/0.53  fof(f213,plain,(
% 1.29/0.53    ~r1_tarski(k1_setfam_1(sK2),sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | (~spl3_6 | ~spl3_7)),
% 1.29/0.53    inference(superposition,[],[f209,f49])).
% 1.29/0.53  fof(f209,plain,(
% 1.29/0.53    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,k1_xboole_0)) | (~spl3_6 | ~spl3_7)),
% 1.29/0.53    inference(forward_demodulation,[],[f134,f121])).
% 1.29/0.53  fof(f134,plain,(
% 1.29/0.53    ~r1_tarski(k1_setfam_1(sK2),k8_setfam_1(sK0,sK1)) | ~spl3_7),
% 1.29/0.53    inference(backward_demodulation,[],[f29,f126])).
% 1.29/0.53  fof(f126,plain,(
% 1.29/0.53    k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2) | ~spl3_7),
% 1.29/0.53    inference(avatar_component_clause,[],[f124])).
% 1.29/0.53  fof(f196,plain,(
% 1.29/0.53    ~spl3_6 | spl3_12),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f194])).
% 1.29/0.53  fof(f194,plain,(
% 1.29/0.53    $false | (~spl3_6 | spl3_12)),
% 1.29/0.53    inference(resolution,[],[f182,f150])).
% 1.29/0.53  fof(f182,plain,(
% 1.29/0.53    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_12),
% 1.29/0.53    inference(avatar_component_clause,[],[f180])).
% 1.29/0.53  fof(f175,plain,(
% 1.29/0.53    spl3_10),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f173])).
% 1.29/0.53  fof(f173,plain,(
% 1.29/0.53    $false | spl3_10),
% 1.29/0.53    inference(resolution,[],[f167,f27])).
% 1.29/0.53  fof(f27,plain,(
% 1.29/0.53    m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.29/0.53    inference(cnf_transformation,[],[f23])).
% 1.29/0.53  fof(f167,plain,(
% 1.29/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl3_10),
% 1.29/0.53    inference(avatar_component_clause,[],[f165])).
% 1.29/0.53  fof(f165,plain,(
% 1.29/0.53    spl3_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.29/0.53  fof(f172,plain,(
% 1.29/0.53    ~spl3_10 | spl3_11 | ~spl3_7),
% 1.29/0.53    inference(avatar_split_clause,[],[f163,f124,f169,f165])).
% 1.29/0.53  fof(f163,plain,(
% 1.29/0.53    m1_subset_1(k1_setfam_1(sK2),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k1_zfmisc_1(sK0))) | ~spl3_7),
% 1.29/0.53    inference(superposition,[],[f37,f126])).
% 1.29/0.53  fof(f149,plain,(
% 1.29/0.53    spl3_9),
% 1.29/0.53    inference(avatar_contradiction_clause,[],[f146])).
% 1.29/0.53  fof(f146,plain,(
% 1.29/0.53    $false | spl3_9),
% 1.29/0.53    inference(resolution,[],[f144,f28])).
% 1.29/0.53  fof(f144,plain,(
% 1.29/0.53    ~r1_tarski(sK1,sK2) | spl3_9),
% 1.29/0.53    inference(avatar_component_clause,[],[f142])).
% 1.29/0.53  fof(f142,plain,(
% 1.29/0.53    spl3_9 <=> r1_tarski(sK1,sK2)),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.29/0.53  fof(f145,plain,(
% 1.29/0.53    ~spl3_9 | spl3_6 | ~spl3_5 | ~spl3_7),
% 1.29/0.53    inference(avatar_split_clause,[],[f138,f124,f115,f119,f142])).
% 1.29/0.53  fof(f115,plain,(
% 1.29/0.53    spl3_5 <=> k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 1.29/0.53    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.29/0.53  fof(f138,plain,(
% 1.29/0.53    k1_xboole_0 = sK1 | ~r1_tarski(sK1,sK2) | (~spl3_5 | ~spl3_7)),
% 1.29/0.53    inference(resolution,[],[f135,f35])).
% 1.29/0.53  fof(f35,plain,(
% 1.29/0.53    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1)) )),
% 1.29/0.53    inference(cnf_transformation,[],[f17])).
% 1.29/0.53  fof(f17,plain,(
% 1.29/0.53    ! [X0,X1] : (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0 | ~r1_tarski(X0,X1))),
% 1.29/0.53    inference(flattening,[],[f16])).
% 1.29/0.53  fof(f16,plain,(
% 1.29/0.53    ! [X0,X1] : ((r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0) | ~r1_tarski(X0,X1))),
% 1.29/0.53    inference(ennf_transformation,[],[f11])).
% 1.29/0.53  fof(f11,axiom,(
% 1.29/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => (r1_tarski(k1_setfam_1(X1),k1_setfam_1(X0)) | k1_xboole_0 = X0))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).
% 1.29/0.53  fof(f135,plain,(
% 1.29/0.53    ~r1_tarski(k1_setfam_1(sK2),k1_setfam_1(sK1)) | (~spl3_5 | ~spl3_7)),
% 1.29/0.53    inference(backward_demodulation,[],[f134,f117])).
% 1.29/0.53  fof(f117,plain,(
% 1.29/0.53    k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1) | ~spl3_5),
% 1.29/0.53    inference(avatar_component_clause,[],[f115])).
% 1.29/0.53  fof(f131,plain,(
% 1.29/0.53    spl3_7 | spl3_8),
% 1.29/0.53    inference(avatar_split_clause,[],[f110,f128,f124])).
% 1.29/0.53  fof(f110,plain,(
% 1.29/0.53    k1_xboole_0 = sK2 | k8_setfam_1(sK0,sK2) = k1_setfam_1(sK2)),
% 1.29/0.53    inference(resolution,[],[f88,f27])).
% 1.29/0.53  fof(f88,plain,(
% 1.29/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | k1_xboole_0 = X3 | k1_setfam_1(X3) = k8_setfam_1(X2,X3)) )),
% 1.29/0.53    inference(duplicate_literal_removal,[],[f85])).
% 1.29/0.53  fof(f85,plain,(
% 1.29/0.53    ( ! [X2,X3] : (k1_setfam_1(X3) = k8_setfam_1(X2,X3) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(X2)))) )),
% 1.29/0.53    inference(superposition,[],[f38,f36])).
% 1.29/0.53  fof(f36,plain,(
% 1.29/0.53    ( ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f18])).
% 1.29/0.53  fof(f18,plain,(
% 1.29/0.53    ! [X0,X1] : (k6_setfam_1(X0,X1) = k1_setfam_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 1.29/0.53    inference(ennf_transformation,[],[f8])).
% 1.29/0.53  fof(f8,axiom,(
% 1.29/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k6_setfam_1(X0,X1) = k1_setfam_1(X1))),
% 1.29/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).
% 1.29/0.53  fof(f38,plain,(
% 1.29/0.53    ( ! [X0,X1] : (k8_setfam_1(X0,X1) = k6_setfam_1(X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 1.29/0.53    inference(cnf_transformation,[],[f20])).
% 1.29/0.53  fof(f122,plain,(
% 1.29/0.53    spl3_5 | spl3_6),
% 1.29/0.53    inference(avatar_split_clause,[],[f109,f119,f115])).
% 1.29/0.53  fof(f109,plain,(
% 1.29/0.53    k1_xboole_0 = sK1 | k8_setfam_1(sK0,sK1) = k1_setfam_1(sK1)),
% 1.29/0.53    inference(resolution,[],[f88,f26])).
% 1.29/0.53  % SZS output end Proof for theBenchmark
% 1.29/0.53  % (18854)------------------------------
% 1.29/0.53  % (18854)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (18854)Termination reason: Refutation
% 1.29/0.53  
% 1.29/0.53  % (18854)Memory used [KB]: 6268
% 1.29/0.53  % (18854)Time elapsed: 0.120 s
% 1.29/0.53  % (18854)------------------------------
% 1.29/0.53  % (18854)------------------------------
% 1.29/0.53  % (18835)Success in time 0.174 s
%------------------------------------------------------------------------------
