%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 567 expanded)
%              Number of leaves         :   24 ( 184 expanded)
%              Depth                    :   16
%              Number of atoms          :  254 ( 959 expanded)
%              Number of equality atoms :   78 ( 473 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f819,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f287,f594,f669,f813,f818])).

fof(f818,plain,
    ( spl3_2
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f816])).

fof(f816,plain,
    ( $false
    | spl3_2
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(resolution,[],[f799,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f799,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_2
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f376,f793])).

fof(f793,plain,
    ( sK0 = k4_subset_1(sK0,sK0,sK1)
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f339,f792])).

fof(f792,plain,
    ( sK0 = k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f782,f57])).

fof(f57,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f37,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f782,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(sK0,sK1))) = k3_tarski(k1_enumset1(sK0,sK0,k1_xboole_0))
    | ~ spl3_15 ),
    inference(superposition,[],[f60,f592])).

fof(f592,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f590])).

% (32001)Refutation not found, incomplete strategy% (32001)------------------------------
% (32001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32001)Termination reason: Refutation not found, incomplete strategy

% (32001)Memory used [KB]: 10618
% (32001)Time elapsed: 0.162 s
% (32001)------------------------------
% (32001)------------------------------
fof(f590,plain,
    ( spl3_15
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f60,plain,(
    ! [X0,X1] : k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f45,f55,f55])).

fof(f45,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f339,plain,
    ( k4_subset_1(sK0,sK0,sK1) = k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f338,f156])).

fof(f156,plain,(
    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(resolution,[],[f150,f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f38,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

% (32021)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (32021)Refutation not found, incomplete strategy% (32021)------------------------------
% (32021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (32021)Termination reason: Refutation not found, incomplete strategy

% (32021)Memory used [KB]: 10746
% (32021)Time elapsed: 0.171 s
% (32021)------------------------------
% (32021)------------------------------
% (31991)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (31991)Refutation not found, incomplete strategy% (31991)------------------------------
% (31991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31991)Termination reason: Refutation not found, incomplete strategy

% (31991)Memory used [KB]: 1663
% (31991)Time elapsed: 0.153 s
% (31991)------------------------------
% (31991)------------------------------
% (32024)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (32015)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
fof(f38,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f150,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,X0,sK1) = k3_tarski(k1_enumset1(X0,X0,sK1)) ) ),
    inference(resolution,[],[f62,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f338,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f337,f58])).

fof(f58,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f41,f41])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f337,plain,
    ( k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f336,f58])).

fof(f336,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)) = k3_tarski(k1_enumset1(sK1,sK1,sK0))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f335,f60])).

fof(f335,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1)))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f331,f58])).

fof(f331,plain,
    ( k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)) = k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1))
    | ~ spl3_5 ),
    inference(superposition,[],[f60,f291])).

fof(f291,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl3_5 ),
    inference(resolution,[],[f271,f98])).

fof(f98,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(X4,X5)
      | k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4 ) ),
    inference(superposition,[],[f59,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f59,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f40,f44,f44])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f271,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f269])).

fof(f269,plain,
    ( spl3_5
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f376,plain,
    ( ~ r1_tarski(k4_subset_1(sK0,sK0,sK1),sK0)
    | spl3_2 ),
    inference(backward_demodulation,[],[f78,f372])).

fof(f372,plain,(
    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1) ),
    inference(forward_demodulation,[],[f371,f156])).

fof(f371,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK0,sK0,sK1)) ),
    inference(forward_demodulation,[],[f368,f58])).

fof(f368,plain,(
    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK0)) ),
    inference(resolution,[],[f152,f33])).

fof(f152,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | k4_subset_1(X3,X4,X3) = k3_tarski(k1_enumset1(X4,X4,X3)) ) ),
    inference(resolution,[],[f62,f66])).

fof(f78,plain,
    ( ~ r1_tarski(k4_subset_1(sK0,sK1,sK0),sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl3_2
  <=> r1_tarski(k4_subset_1(sK0,sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f813,plain,
    ( spl3_1
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f811])).

fof(f811,plain,
    ( $false
    | spl3_1
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(resolution,[],[f798,f63])).

fof(f798,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl3_1
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f375,f793])).

fof(f375,plain,
    ( ~ r1_tarski(sK0,k4_subset_1(sK0,sK0,sK1))
    | spl3_1 ),
    inference(backward_demodulation,[],[f74,f372])).

fof(f74,plain,
    ( ~ r1_tarski(sK0,k4_subset_1(sK0,sK1,sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_subset_1(sK0,sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f669,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f660])).

fof(f660,plain,
    ( $false
    | spl3_14 ),
    inference(resolution,[],[f653,f588])).

fof(f588,plain,
    ( ~ r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f586])).

fof(f586,plain,
    ( spl3_14
  <=> r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f653,plain,
    ( r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | spl3_14 ),
    inference(resolution,[],[f625,f255])).

fof(f255,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK2(k1_xboole_0,X1),X2)
      | r1_tarski(k1_xboole_0,X1) ) ),
    inference(resolution,[],[f88,f36])).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X2))
      | r2_hidden(sK2(X0,X1),X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f47,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f625,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))
    | spl3_14 ),
    inference(resolution,[],[f588,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK2(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f594,plain,
    ( ~ spl3_14
    | spl3_15
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f573,f269,f590,f586])).

fof(f573,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)
    | ~ r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1))
    | ~ spl3_5 ),
    inference(superposition,[],[f61,f511])).

fof(f511,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1)))
    | ~ spl3_5 ),
    inference(superposition,[],[f507,f117])).

fof(f117,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X2,X2) ),
    inference(superposition,[],[f59,f114])).

fof(f114,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f110,f84])).

fof(f84,plain,(
    ! [X0] : k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0 ),
    inference(superposition,[],[f57,f58])).

fof(f110,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X2)) ),
    inference(superposition,[],[f60,f84])).

fof(f507,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl3_5 ),
    inference(superposition,[],[f333,f92])).

fof(f92,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(resolution,[],[f91,f63])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f56,f61])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f333,plain,
    ( k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))
    | ~ spl3_5 ),
    inference(superposition,[],[f100,f291])).

fof(f100,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f56,f59])).

fof(f287,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl3_5 ),
    inference(resolution,[],[f279,f270])).

fof(f270,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f269])).

fof(f279,plain,
    ( r1_tarski(sK1,sK0)
    | spl3_5 ),
    inference(resolution,[],[f278,f254])).

fof(f254,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f88,f33])).

fof(f278,plain,
    ( ~ r2_hidden(sK2(sK1,sK0),sK0)
    | spl3_5 ),
    inference(resolution,[],[f270,f53])).

fof(f80,plain,
    ( ~ spl3_2
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f68,f72,f76])).

fof(f68,plain,
    ( ~ r1_tarski(sK0,k4_subset_1(sK0,sK1,sK0))
    | ~ r1_tarski(k4_subset_1(sK0,sK1,sK0),sK0) ),
    inference(extensionality_resolution,[],[f50,f65])).

fof(f65,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f34,f35])).

fof(f34,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f26])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.52  % (32004)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (31996)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (32014)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (32011)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (32000)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (32000)Refutation not found, incomplete strategy% (32000)------------------------------
% 0.20/0.54  % (32000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32000)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (32000)Memory used [KB]: 10618
% 0.20/0.54  % (32000)Time elapsed: 0.111 s
% 0.20/0.54  % (32000)------------------------------
% 0.20/0.54  % (32000)------------------------------
% 0.20/0.54  % (31994)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (32014)Refutation not found, incomplete strategy% (32014)------------------------------
% 0.20/0.54  % (32014)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (32014)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (32014)Memory used [KB]: 1663
% 0.20/0.54  % (32014)Time elapsed: 0.130 s
% 0.20/0.54  % (32014)------------------------------
% 0.20/0.54  % (32014)------------------------------
% 0.20/0.55  % (32002)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.55  % (32022)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (31995)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (32003)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (32009)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (31995)Refutation not found, incomplete strategy% (31995)------------------------------
% 0.20/0.55  % (31995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (32009)Refutation not found, incomplete strategy% (32009)------------------------------
% 0.20/0.55  % (32009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (32009)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (32009)Memory used [KB]: 10618
% 0.20/0.55  % (32009)Time elapsed: 0.135 s
% 0.20/0.55  % (32009)------------------------------
% 0.20/0.55  % (32009)------------------------------
% 0.20/0.55  % (32002)Refutation not found, incomplete strategy% (32002)------------------------------
% 0.20/0.55  % (32002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (32002)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (32002)Memory used [KB]: 10746
% 0.20/0.55  % (32002)Time elapsed: 0.132 s
% 0.20/0.55  % (32002)------------------------------
% 0.20/0.55  % (32002)------------------------------
% 0.20/0.56  % (32012)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.56  % (31995)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (31995)Memory used [KB]: 6140
% 0.20/0.56  % (31995)Time elapsed: 0.137 s
% 0.20/0.56  % (31995)------------------------------
% 0.20/0.56  % (31995)------------------------------
% 0.20/0.56  % (31993)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.56  % (32012)Refutation not found, incomplete strategy% (32012)------------------------------
% 0.20/0.56  % (32012)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (32012)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (32012)Memory used [KB]: 10746
% 0.20/0.56  % (32012)Time elapsed: 0.139 s
% 0.20/0.56  % (32012)------------------------------
% 0.20/0.56  % (32012)------------------------------
% 0.20/0.56  % (32008)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.57  % (32003)Refutation found. Thanks to Tanya!
% 0.20/0.57  % SZS status Theorem for theBenchmark
% 0.20/0.57  % (32010)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.57  % (32006)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.58  % (32001)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.58  % (31998)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f819,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f80,f287,f594,f669,f813,f818])).
% 0.20/0.58  fof(f818,plain,(
% 0.20/0.58    spl3_2 | ~spl3_5 | ~spl3_15),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f816])).
% 0.20/0.58  fof(f816,plain,(
% 0.20/0.58    $false | (spl3_2 | ~spl3_5 | ~spl3_15)),
% 0.20/0.58    inference(resolution,[],[f799,f63])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.58    inference(equality_resolution,[],[f49])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.58    inference(cnf_transformation,[],[f28])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.58    inference(flattening,[],[f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.58    inference(nnf_transformation,[],[f3])).
% 0.20/0.58  fof(f3,axiom,(
% 0.20/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.58  fof(f799,plain,(
% 0.20/0.58    ~r1_tarski(sK0,sK0) | (spl3_2 | ~spl3_5 | ~spl3_15)),
% 0.20/0.58    inference(backward_demodulation,[],[f376,f793])).
% 0.20/0.58  fof(f793,plain,(
% 0.20/0.58    sK0 = k4_subset_1(sK0,sK0,sK1) | (~spl3_5 | ~spl3_15)),
% 0.20/0.58    inference(backward_demodulation,[],[f339,f792])).
% 0.20/0.58  fof(f792,plain,(
% 0.20/0.58    sK0 = k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(sK0,sK1))) | ~spl3_15),
% 0.20/0.58    inference(forward_demodulation,[],[f782,f57])).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 0.20/0.58    inference(definition_unfolding,[],[f37,f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f42,f41])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f10])).
% 0.20/0.58  fof(f10,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f11])).
% 0.20/0.58  fof(f11,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.58  fof(f782,plain,(
% 0.20/0.58    k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(sK0,sK1))) = k3_tarski(k1_enumset1(sK0,sK0,k1_xboole_0)) | ~spl3_15),
% 0.20/0.58    inference(superposition,[],[f60,f592])).
% 0.20/0.58  fof(f592,plain,(
% 0.20/0.58    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) | ~spl3_15),
% 0.20/0.58    inference(avatar_component_clause,[],[f590])).
% 0.20/0.58  % (32001)Refutation not found, incomplete strategy% (32001)------------------------------
% 0.20/0.58  % (32001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.58  % (32001)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.58  
% 0.20/0.58  % (32001)Memory used [KB]: 10618
% 0.20/0.58  % (32001)Time elapsed: 0.162 s
% 0.20/0.58  % (32001)------------------------------
% 0.20/0.58  % (32001)------------------------------
% 0.20/0.58  fof(f590,plain,(
% 0.20/0.58    spl3_15 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.58  fof(f60,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k3_tarski(k1_enumset1(X0,X0,X1)) = k3_tarski(k1_enumset1(X0,X0,k4_xboole_0(X1,X0)))) )),
% 0.20/0.58    inference(definition_unfolding,[],[f45,f55,f55])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.58  fof(f339,plain,(
% 0.20/0.58    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(sK0,sK1))) | ~spl3_5),
% 0.20/0.58    inference(forward_demodulation,[],[f338,f156])).
% 0.20/0.58  fof(f156,plain,(
% 0.20/0.58    k4_subset_1(sK0,sK0,sK1) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 0.20/0.58    inference(resolution,[],[f150,f66])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.58    inference(forward_demodulation,[],[f38,f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.58    inference(cnf_transformation,[],[f12])).
% 0.20/0.58  fof(f12,axiom,(
% 0.20/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.59/0.58  % (32021)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.59/0.58  % (32021)Refutation not found, incomplete strategy% (32021)------------------------------
% 1.59/0.58  % (32021)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (32021)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (32021)Memory used [KB]: 10746
% 1.59/0.58  % (32021)Time elapsed: 0.171 s
% 1.59/0.58  % (32021)------------------------------
% 1.59/0.58  % (32021)------------------------------
% 1.59/0.58  % (31991)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.59/0.58  % (31991)Refutation not found, incomplete strategy% (31991)------------------------------
% 1.59/0.58  % (31991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (31991)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (31991)Memory used [KB]: 1663
% 1.59/0.58  % (31991)Time elapsed: 0.153 s
% 1.59/0.58  % (31991)------------------------------
% 1.59/0.58  % (31991)------------------------------
% 1.59/0.59  % (32024)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.59/0.59  % (32015)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.59/0.59  fof(f38,plain,(
% 1.59/0.59    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f13])).
% 1.59/0.59  fof(f13,axiom,(
% 1.59/0.59    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.59/0.59  fof(f150,plain,(
% 1.59/0.59    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,X0,sK1) = k3_tarski(k1_enumset1(X0,X0,sK1))) )),
% 1.59/0.59    inference(resolution,[],[f62,f33])).
% 1.59/0.59  fof(f33,plain,(
% 1.59/0.59    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.59/0.59    inference(cnf_transformation,[],[f26])).
% 1.59/0.59  fof(f26,plain,(
% 1.59/0.59    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f25])).
% 1.59/0.59  fof(f25,plain,(
% 1.59/0.59    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f19,plain,(
% 1.59/0.59    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.59    inference(ennf_transformation,[],[f18])).
% 1.59/0.59  fof(f18,negated_conjecture,(
% 1.59/0.59    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.59/0.59    inference(negated_conjecture,[],[f17])).
% 1.59/0.59  fof(f17,conjecture,(
% 1.59/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 1.59/0.59  fof(f62,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k3_tarski(k1_enumset1(X1,X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/0.59    inference(definition_unfolding,[],[f54,f55])).
% 1.59/0.59  fof(f54,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f24])).
% 1.59/0.59  fof(f24,plain,(
% 1.59/0.59    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.59    inference(flattening,[],[f23])).
% 1.59/0.59  fof(f23,plain,(
% 1.59/0.59    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.59/0.59    inference(ennf_transformation,[],[f15])).
% 1.59/0.59  fof(f15,axiom,(
% 1.59/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.59/0.59  fof(f338,plain,(
% 1.59/0.59    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(sK0,sK0,k4_xboole_0(sK0,sK1))) | ~spl3_5),
% 1.59/0.59    inference(forward_demodulation,[],[f337,f58])).
% 1.59/0.59  fof(f58,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f39,f41,f41])).
% 1.59/0.59  fof(f39,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f9])).
% 1.59/0.59  fof(f9,axiom,(
% 1.59/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.59/0.59  fof(f337,plain,(
% 1.59/0.59    k3_tarski(k1_enumset1(sK0,sK0,sK1)) = k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)) | ~spl3_5),
% 1.59/0.59    inference(forward_demodulation,[],[f336,f58])).
% 1.59/0.59  fof(f336,plain,(
% 1.59/0.59    k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)) = k3_tarski(k1_enumset1(sK1,sK1,sK0)) | ~spl3_5),
% 1.59/0.59    inference(forward_demodulation,[],[f335,f60])).
% 1.59/0.59  fof(f335,plain,(
% 1.59/0.59    k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)) = k3_tarski(k1_enumset1(sK1,sK1,k4_xboole_0(sK0,sK1))) | ~spl3_5),
% 1.59/0.59    inference(forward_demodulation,[],[f331,f58])).
% 1.59/0.59  fof(f331,plain,(
% 1.59/0.59    k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK0)) = k3_tarski(k1_enumset1(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1),sK1)) | ~spl3_5),
% 1.59/0.59    inference(superposition,[],[f60,f291])).
% 1.59/0.59  fof(f291,plain,(
% 1.59/0.59    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl3_5),
% 1.59/0.59    inference(resolution,[],[f271,f98])).
% 1.59/0.59  fof(f98,plain,(
% 1.59/0.59    ( ! [X4,X5] : (~r1_tarski(X4,X5) | k4_xboole_0(X5,k4_xboole_0(X5,X4)) = X4) )),
% 1.59/0.59    inference(superposition,[],[f59,f61])).
% 1.59/0.59  fof(f61,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(definition_unfolding,[],[f46,f44])).
% 1.59/0.59  fof(f44,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f8])).
% 1.59/0.59  fof(f8,axiom,(
% 1.59/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.59/0.59  fof(f46,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f20])).
% 1.59/0.59  fof(f20,plain,(
% 1.59/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.59/0.59    inference(ennf_transformation,[],[f6])).
% 1.59/0.59  fof(f6,axiom,(
% 1.59/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.59/0.59  fof(f59,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.59/0.59    inference(definition_unfolding,[],[f40,f44,f44])).
% 1.59/0.59  fof(f40,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f1])).
% 1.59/0.59  fof(f1,axiom,(
% 1.59/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.59/0.59  fof(f271,plain,(
% 1.59/0.59    r1_tarski(sK1,sK0) | ~spl3_5),
% 1.59/0.59    inference(avatar_component_clause,[],[f269])).
% 1.59/0.59  fof(f269,plain,(
% 1.59/0.59    spl3_5 <=> r1_tarski(sK1,sK0)),
% 1.59/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.59/0.59  fof(f376,plain,(
% 1.59/0.59    ~r1_tarski(k4_subset_1(sK0,sK0,sK1),sK0) | spl3_2),
% 1.59/0.59    inference(backward_demodulation,[],[f78,f372])).
% 1.59/0.59  fof(f372,plain,(
% 1.59/0.59    k4_subset_1(sK0,sK1,sK0) = k4_subset_1(sK0,sK0,sK1)),
% 1.59/0.59    inference(forward_demodulation,[],[f371,f156])).
% 1.59/0.59  fof(f371,plain,(
% 1.59/0.59    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK0,sK0,sK1))),
% 1.59/0.59    inference(forward_demodulation,[],[f368,f58])).
% 1.59/0.59  fof(f368,plain,(
% 1.59/0.59    k4_subset_1(sK0,sK1,sK0) = k3_tarski(k1_enumset1(sK1,sK1,sK0))),
% 1.59/0.59    inference(resolution,[],[f152,f33])).
% 1.59/0.59  fof(f152,plain,(
% 1.59/0.59    ( ! [X4,X3] : (~m1_subset_1(X4,k1_zfmisc_1(X3)) | k4_subset_1(X3,X4,X3) = k3_tarski(k1_enumset1(X4,X4,X3))) )),
% 1.59/0.59    inference(resolution,[],[f62,f66])).
% 1.59/0.59  fof(f78,plain,(
% 1.59/0.59    ~r1_tarski(k4_subset_1(sK0,sK1,sK0),sK0) | spl3_2),
% 1.59/0.59    inference(avatar_component_clause,[],[f76])).
% 1.59/0.59  fof(f76,plain,(
% 1.59/0.59    spl3_2 <=> r1_tarski(k4_subset_1(sK0,sK1,sK0),sK0)),
% 1.59/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.59/0.59  fof(f813,plain,(
% 1.59/0.59    spl3_1 | ~spl3_5 | ~spl3_15),
% 1.59/0.59    inference(avatar_contradiction_clause,[],[f811])).
% 1.59/0.59  fof(f811,plain,(
% 1.59/0.59    $false | (spl3_1 | ~spl3_5 | ~spl3_15)),
% 1.59/0.59    inference(resolution,[],[f798,f63])).
% 1.59/0.59  fof(f798,plain,(
% 1.59/0.59    ~r1_tarski(sK0,sK0) | (spl3_1 | ~spl3_5 | ~spl3_15)),
% 1.59/0.59    inference(backward_demodulation,[],[f375,f793])).
% 1.59/0.59  fof(f375,plain,(
% 1.59/0.59    ~r1_tarski(sK0,k4_subset_1(sK0,sK0,sK1)) | spl3_1),
% 1.59/0.59    inference(backward_demodulation,[],[f74,f372])).
% 1.59/0.59  fof(f74,plain,(
% 1.59/0.59    ~r1_tarski(sK0,k4_subset_1(sK0,sK1,sK0)) | spl3_1),
% 1.59/0.59    inference(avatar_component_clause,[],[f72])).
% 1.59/0.59  fof(f72,plain,(
% 1.59/0.59    spl3_1 <=> r1_tarski(sK0,k4_subset_1(sK0,sK1,sK0))),
% 1.59/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.59/0.59  fof(f669,plain,(
% 1.59/0.59    spl3_14),
% 1.59/0.59    inference(avatar_contradiction_clause,[],[f660])).
% 1.59/0.59  fof(f660,plain,(
% 1.59/0.59    $false | spl3_14),
% 1.59/0.59    inference(resolution,[],[f653,f588])).
% 1.59/0.59  fof(f588,plain,(
% 1.59/0.59    ~r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) | spl3_14),
% 1.59/0.59    inference(avatar_component_clause,[],[f586])).
% 1.59/0.59  fof(f586,plain,(
% 1.59/0.59    spl3_14 <=> r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1))),
% 1.59/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.59/0.59  fof(f653,plain,(
% 1.59/0.59    r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) | spl3_14),
% 1.59/0.59    inference(resolution,[],[f625,f255])).
% 1.59/0.59  fof(f255,plain,(
% 1.59/0.59    ( ! [X2,X1] : (r2_hidden(sK2(k1_xboole_0,X1),X2) | r1_tarski(k1_xboole_0,X1)) )),
% 1.59/0.59    inference(resolution,[],[f88,f36])).
% 1.59/0.59  fof(f36,plain,(
% 1.59/0.59    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f16])).
% 1.59/0.59  fof(f16,axiom,(
% 1.59/0.59    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.59/0.59  fof(f88,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X2)) | r2_hidden(sK2(X0,X1),X2) | r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(resolution,[],[f47,f52])).
% 1.59/0.59  fof(f52,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f32])).
% 1.59/0.59  fof(f32,plain,(
% 1.59/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).
% 1.59/0.59  fof(f31,plain,(
% 1.59/0.59    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 1.59/0.59    introduced(choice_axiom,[])).
% 1.59/0.59  fof(f30,plain,(
% 1.59/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.59    inference(rectify,[],[f29])).
% 1.59/0.59  fof(f29,plain,(
% 1.59/0.59    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.59/0.59    inference(nnf_transformation,[],[f22])).
% 1.59/0.59  fof(f22,plain,(
% 1.59/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.59/0.59    inference(ennf_transformation,[],[f2])).
% 1.59/0.59  fof(f2,axiom,(
% 1.59/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.59/0.59  fof(f47,plain,(
% 1.59/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f21])).
% 1.59/0.59  fof(f21,plain,(
% 1.59/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.59/0.59    inference(ennf_transformation,[],[f14])).
% 1.59/0.59  fof(f14,axiom,(
% 1.59/0.59    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.59/0.59  fof(f625,plain,(
% 1.59/0.59    ~r2_hidden(sK2(k1_xboole_0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)) | spl3_14),
% 1.59/0.59    inference(resolution,[],[f588,f53])).
% 1.59/0.59  fof(f53,plain,(
% 1.59/0.59    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK2(X0,X1),X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f32])).
% 1.59/0.59  fof(f594,plain,(
% 1.59/0.59    ~spl3_14 | spl3_15 | ~spl3_5),
% 1.59/0.59    inference(avatar_split_clause,[],[f573,f269,f590,f586])).
% 1.59/0.59  fof(f573,plain,(
% 1.59/0.59    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) | ~r1_tarski(k1_xboole_0,k4_xboole_0(sK0,sK1)) | ~spl3_5),
% 1.59/0.59    inference(superposition,[],[f61,f511])).
% 1.59/0.59  fof(f511,plain,(
% 1.59/0.59    k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(sK0,sK1))) | ~spl3_5),
% 1.59/0.59    inference(superposition,[],[f507,f117])).
% 1.59/0.59  fof(f117,plain,(
% 1.59/0.59    ( ! [X2] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)) = k4_xboole_0(X2,X2)) )),
% 1.59/0.59    inference(superposition,[],[f59,f114])).
% 1.59/0.59  fof(f114,plain,(
% 1.59/0.59    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.59/0.59    inference(forward_demodulation,[],[f110,f84])).
% 1.59/0.59  fof(f84,plain,(
% 1.59/0.59    ( ! [X0] : (k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) = X0) )),
% 1.59/0.59    inference(superposition,[],[f57,f58])).
% 1.59/0.59  fof(f110,plain,(
% 1.59/0.59    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k3_tarski(k1_enumset1(k1_xboole_0,k1_xboole_0,X2))) )),
% 1.59/0.59    inference(superposition,[],[f60,f84])).
% 1.59/0.59  fof(f507,plain,(
% 1.59/0.59    k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl3_5),
% 1.59/0.59    inference(superposition,[],[f333,f92])).
% 1.59/0.59  fof(f92,plain,(
% 1.59/0.59    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.59/0.59    inference(resolution,[],[f91,f63])).
% 1.59/0.59  fof(f91,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)) )),
% 1.59/0.59    inference(superposition,[],[f56,f61])).
% 1.59/0.59  fof(f56,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.59/0.59    inference(definition_unfolding,[],[f43,f44])).
% 1.59/0.59  fof(f43,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.59/0.59    inference(cnf_transformation,[],[f4])).
% 1.59/0.59  fof(f4,axiom,(
% 1.59/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.59/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.59/0.59  fof(f333,plain,(
% 1.59/0.59    k4_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) | ~spl3_5),
% 1.59/0.59    inference(superposition,[],[f100,f291])).
% 1.59/0.59  fof(f100,plain,(
% 1.59/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 1.59/0.59    inference(superposition,[],[f56,f59])).
% 1.59/0.59  fof(f287,plain,(
% 1.59/0.59    spl3_5),
% 1.59/0.59    inference(avatar_contradiction_clause,[],[f280])).
% 1.59/0.59  fof(f280,plain,(
% 1.59/0.59    $false | spl3_5),
% 1.59/0.59    inference(resolution,[],[f279,f270])).
% 1.59/0.59  fof(f270,plain,(
% 1.59/0.59    ~r1_tarski(sK1,sK0) | spl3_5),
% 1.59/0.59    inference(avatar_component_clause,[],[f269])).
% 1.59/0.59  fof(f279,plain,(
% 1.59/0.59    r1_tarski(sK1,sK0) | spl3_5),
% 1.59/0.59    inference(resolution,[],[f278,f254])).
% 1.59/0.59  fof(f254,plain,(
% 1.59/0.59    ( ! [X0] : (r2_hidden(sK2(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 1.59/0.59    inference(resolution,[],[f88,f33])).
% 1.59/0.59  fof(f278,plain,(
% 1.59/0.59    ~r2_hidden(sK2(sK1,sK0),sK0) | spl3_5),
% 1.59/0.59    inference(resolution,[],[f270,f53])).
% 1.59/0.59  fof(f80,plain,(
% 1.59/0.59    ~spl3_2 | ~spl3_1),
% 1.59/0.59    inference(avatar_split_clause,[],[f68,f72,f76])).
% 1.59/0.59  fof(f68,plain,(
% 1.59/0.59    ~r1_tarski(sK0,k4_subset_1(sK0,sK1,sK0)) | ~r1_tarski(k4_subset_1(sK0,sK1,sK0),sK0)),
% 1.59/0.59    inference(extensionality_resolution,[],[f50,f65])).
% 1.59/0.59  fof(f65,plain,(
% 1.59/0.59    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 1.59/0.59    inference(backward_demodulation,[],[f34,f35])).
% 1.59/0.59  fof(f34,plain,(
% 1.59/0.59    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 1.59/0.59    inference(cnf_transformation,[],[f26])).
% 1.59/0.59  fof(f50,plain,(
% 1.59/0.59    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.59/0.59    inference(cnf_transformation,[],[f28])).
% 1.59/0.59  % SZS output end Proof for theBenchmark
% 1.59/0.59  % (32003)------------------------------
% 1.59/0.59  % (32003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.59  % (32003)Termination reason: Refutation
% 1.59/0.59  
% 1.59/0.59  % (32003)Memory used [KB]: 6780
% 1.59/0.59  % (32003)Time elapsed: 0.155 s
% 1.59/0.59  % (32003)------------------------------
% 1.59/0.59  % (32003)------------------------------
% 1.59/0.59  % (31997)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.59/0.59  % (31989)Success in time 0.226 s
%------------------------------------------------------------------------------
