%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 217 expanded)
%              Number of leaves         :   21 (  67 expanded)
%              Depth                    :   15
%              Number of atoms          :  138 ( 311 expanded)
%              Number of equality atoms :   71 ( 194 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f270,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f90,f92,f269])).

fof(f269,plain,(
    ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f268])).

fof(f268,plain,
    ( $false
    | ~ spl2_2 ),
    inference(trivial_inequality_removal,[],[f267])).

% (23335)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
fof(f267,plain,
    ( sK0 != sK0
    | ~ spl2_2 ),
    inference(superposition,[],[f60,f259])).

fof(f259,plain,
    ( sK0 = k4_subset_1(sK0,sK1,sK0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f258,f134])).

fof(f134,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f132,f63])).

fof(f63,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(resolution,[],[f47,f61])).

fof(f61,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f38,f54])).

fof(f54,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f36,f43])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f132,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f57,f55])).

fof(f55,plain,(
    ! [X0] : k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f37,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f53])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f258,plain,
    ( k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f254,f122])).

fof(f122,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK0)
    | ~ spl2_2 ),
    inference(superposition,[],[f62,f118])).

fof(f118,plain,
    ( sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f93,f117])).

fof(f117,plain,(
    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f112,f76])).

fof(f76,plain,(
    k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0))
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f112,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f46,f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f93,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f89,f45])).

fof(f89,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_2
  <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f62,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f47,f38])).

fof(f254,plain,(
    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f245,f141])).

fof(f141,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(X4,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f130,f57])).

fof(f130,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0)) ),
    inference(superposition,[],[f57,f56])).

fof(f56,plain,(
    ! [X0,X1] : k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f39,f52,f52])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f245,plain,(
    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f242,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f35,f34])).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f242,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(sK0))
      | k4_subset_1(sK0,sK1,X8) = k5_xboole_0(sK1,k4_xboole_0(X8,sK1)) ) ),
    inference(resolution,[],[f174,f32])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1)) ) ),
    inference(forward_demodulation,[],[f58,f57])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f49,f53])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f60,plain,(
    sK0 != k4_subset_1(sK0,sK1,sK0) ),
    inference(forward_demodulation,[],[f33,f34])).

fof(f33,plain,(
    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f85,f32])).

fof(f85,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_1
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f90,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f80,f87,f83])).

fof(f80,plain,
    ( m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f44,f76])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:36:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (23337)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (23338)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (23332)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (23341)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.46  % (23347)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (23336)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (23342)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.47  % (23334)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.47  % (23346)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (23334)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (23348)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (23340)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (23339)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (23345)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (23333)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (23343)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f270,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f90,f92,f269])).
% 0.20/0.48  fof(f269,plain,(
% 0.20/0.48    ~spl2_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f268])).
% 0.20/0.48  fof(f268,plain,(
% 0.20/0.48    $false | ~spl2_2),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f267])).
% 0.20/0.48  % (23335)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  fof(f267,plain,(
% 0.20/0.48    sK0 != sK0 | ~spl2_2),
% 0.20/0.48    inference(superposition,[],[f60,f259])).
% 0.20/0.48  fof(f259,plain,(
% 0.20/0.48    sK0 = k4_subset_1(sK0,sK1,sK0) | ~spl2_2),
% 0.20/0.48    inference(forward_demodulation,[],[f258,f134])).
% 0.20/0.48  fof(f134,plain,(
% 0.20/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.48    inference(forward_demodulation,[],[f132,f63])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 0.20/0.48    inference(resolution,[],[f47,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.20/0.48    inference(superposition,[],[f38,f54])).
% 0.20/0.48  fof(f54,plain,(
% 0.20/0.48    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.20/0.48    inference(definition_unfolding,[],[f36,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.48    inference(rectify,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k4_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.48    inference(unused_predicate_definition_removal,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.20/0.48    inference(superposition,[],[f57,f55])).
% 0.20/0.48  fof(f55,plain,(
% 0.20/0.48    ( ! [X0] : (k3_tarski(k3_enumset1(X0,X0,X0,X0,X0)) = X0) )),
% 0.20/0.48    inference(definition_unfolding,[],[f37,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f40,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f41,f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f48,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.48    inference(rectify,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X0,X0,X0,X0,X1))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f42,f53])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.20/0.48  fof(f258,plain,(
% 0.20/0.48    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k1_xboole_0) | ~spl2_2),
% 0.20/0.48    inference(forward_demodulation,[],[f254,f122])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    k1_xboole_0 = k4_xboole_0(sK1,sK0) | ~spl2_2),
% 0.20/0.48    inference(superposition,[],[f62,f118])).
% 0.20/0.48  fof(f118,plain,(
% 0.20/0.48    sK1 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_2),
% 0.20/0.48    inference(backward_demodulation,[],[f93,f117])).
% 0.20/0.48  fof(f117,plain,(
% 0.20/0.48    sK1 = k3_subset_1(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.48    inference(forward_demodulation,[],[f112,f76])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    k4_xboole_0(sK0,sK1) = k3_subset_1(sK0,sK1)),
% 0.20/0.48    inference(resolution,[],[f45,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0)) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ? [X0,X1] : (k2_subset_1(X0) != k4_subset_1(X0,X1,k2_subset_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.20/0.48    inference(negated_conjecture,[],[f18])).
% 0.20/0.48  fof(f18,conjecture,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k2_subset_1(X0) = k4_subset_1(X0,X1,k2_subset_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 0.20/0.48    inference(resolution,[],[f46,f32])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_subset_1(sK0,k4_xboole_0(sK0,sK1)) | ~spl2_2),
% 0.20/0.48    inference(resolution,[],[f89,f45])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f87])).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    spl2_2 <=> m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.48    inference(resolution,[],[f47,f38])).
% 0.20/0.48  fof(f254,plain,(
% 0.20/0.48    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.20/0.48    inference(superposition,[],[f245,f141])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ( ! [X4,X3] : (k5_xboole_0(X3,k4_xboole_0(X4,X3)) = k5_xboole_0(X4,k4_xboole_0(X3,X4))) )),
% 0.20/0.48    inference(superposition,[],[f130,f57])).
% 0.20/0.48  fof(f130,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X0))) )),
% 0.20/0.48    inference(superposition,[],[f57,f56])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k3_enumset1(X0,X0,X0,X0,X1) = k3_enumset1(X1,X1,X1,X1,X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f39,f52,f52])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.48  fof(f245,plain,(
% 0.20/0.48    k4_subset_1(sK0,sK1,sK0) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 0.20/0.48    inference(resolution,[],[f242,f59])).
% 0.20/0.48  fof(f59,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f35,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,axiom,(
% 0.20/0.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.48  fof(f242,plain,(
% 0.20/0.48    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(sK0)) | k4_subset_1(sK0,sK1,X8) = k5_xboole_0(sK1,k4_xboole_0(X8,sK1))) )),
% 0.20/0.48    inference(resolution,[],[f174,f32])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,X1))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f58,f57])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k3_enumset1(X1,X1,X1,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f49,f53])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(flattening,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 0.20/0.48    inference(ennf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    sK0 != k4_subset_1(sK0,sK1,sK0)),
% 0.20/0.48    inference(forward_demodulation,[],[f33,f34])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    k2_subset_1(sK0) != k4_subset_1(sK0,sK1,k2_subset_1(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f31])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    spl2_1),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f91])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    $false | spl2_1),
% 0.20/0.48    inference(resolution,[],[f85,f32])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(sK0)) | spl2_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f83])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    spl2_1 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ~spl2_1 | spl2_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f80,f87,f83])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    m1_subset_1(k4_xboole_0(sK0,sK1),k1_zfmisc_1(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.20/0.48    inference(superposition,[],[f44,f76])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (23334)------------------------------
% 0.20/0.48  % (23334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23334)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (23334)Memory used [KB]: 6140
% 0.20/0.48  % (23334)Time elapsed: 0.056 s
% 0.20/0.48  % (23334)------------------------------
% 0.20/0.48  % (23334)------------------------------
% 0.20/0.48  % (23331)Success in time 0.128 s
%------------------------------------------------------------------------------
