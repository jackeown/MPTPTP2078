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
% DateTime   : Thu Dec  3 12:46:43 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   52 (  72 expanded)
%              Number of leaves         :   15 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 100 expanded)
%              Number of equality atoms :   24 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f43,f86,f444])).

fof(f444,plain,(
    spl1_5 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | spl1_5 ),
    inference(unit_resulting_resolution,[],[f85,f416,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f416,plain,(
    ! [X10] : r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X10)) ),
    inference(superposition,[],[f48,f374])).

fof(f374,plain,(
    ! [X1] : k1_zfmisc_1(X1) = k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f240,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f240,plain,(
    ! [X1] : k1_zfmisc_1(X1) = k2_xboole_0(k1_zfmisc_1(X1),k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(k1_xboole_0))) ),
    inference(superposition,[],[f124,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f124,plain,(
    ! [X0] : k1_zfmisc_1(X0) = k2_xboole_0(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f98,f26])).

fof(f98,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0)) ),
    inference(superposition,[],[f25,f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).

fof(f48,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f22,f23])).

fof(f85,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl1_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl1_5
  <=> m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f86,plain,
    ( ~ spl1_5
    | spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f76,f40,f35,f83])).

fof(f35,plain,
    ( spl1_1
  <=> m1_subset_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f40,plain,
    ( spl1_2
  <=> k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f76,plain,
    ( ~ m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl1_1
    | ~ spl1_2 ),
    inference(backward_demodulation,[],[f37,f42])).

fof(f42,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f37,plain,
    ( ~ m1_subset_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f43,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f33,f40])).

fof(f33,plain,(
    k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f19,f31])).

fof(f31,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f30])).

fof(f30,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f24,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f24,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f38,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f32,f35])).

fof(f32,plain,(
    ~ m1_subset_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(definition_unfolding,[],[f18,f31])).

fof(f18,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f15])).

fof(f15,plain,
    ( ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
   => ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 16:36:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.40  % (21861)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.41  % (21861)Refutation found. Thanks to Tanya!
% 0.19/0.41  % SZS status Theorem for theBenchmark
% 0.19/0.41  % SZS output start Proof for theBenchmark
% 0.19/0.41  fof(f445,plain,(
% 0.19/0.41    $false),
% 0.19/0.41    inference(avatar_sat_refutation,[],[f38,f43,f86,f444])).
% 0.19/0.41  fof(f444,plain,(
% 0.19/0.41    spl1_5),
% 0.19/0.41    inference(avatar_contradiction_clause,[],[f439])).
% 0.19/0.41  fof(f439,plain,(
% 0.19/0.41    $false | spl1_5),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f85,f416,f28])).
% 0.19/0.41  fof(f28,plain,(
% 0.19/0.41    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f17])).
% 0.19/0.41  fof(f17,plain,(
% 0.19/0.41    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.41    inference(nnf_transformation,[],[f10])).
% 0.19/0.41  fof(f10,axiom,(
% 0.19/0.41    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.41  fof(f416,plain,(
% 0.19/0.41    ( ! [X10] : (r1_tarski(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(X10))) )),
% 0.19/0.41    inference(superposition,[],[f48,f374])).
% 0.19/0.41  fof(f374,plain,(
% 0.19/0.41    ( ! [X1] : (k1_zfmisc_1(X1) = k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(k1_xboole_0))) )),
% 0.19/0.41    inference(superposition,[],[f240,f68])).
% 0.19/0.41  fof(f68,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f22,f26])).
% 0.19/0.41  fof(f26,plain,(
% 0.19/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.41    inference(cnf_transformation,[],[f14])).
% 0.19/0.41  fof(f14,plain,(
% 0.19/0.41    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.41    inference(ennf_transformation,[],[f2])).
% 0.19/0.41  fof(f2,axiom,(
% 0.19/0.41    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.41  fof(f22,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f4])).
% 0.19/0.41  fof(f4,axiom,(
% 0.19/0.41    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.19/0.41  fof(f240,plain,(
% 0.19/0.41    ( ! [X1] : (k1_zfmisc_1(X1) = k2_xboole_0(k1_zfmisc_1(X1),k2_xboole_0(k1_zfmisc_1(X1),k1_zfmisc_1(k1_xboole_0)))) )),
% 0.19/0.41    inference(superposition,[],[f124,f23])).
% 0.19/0.41  fof(f23,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f1])).
% 0.19/0.41  fof(f1,axiom,(
% 0.19/0.41    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.41  fof(f124,plain,(
% 0.19/0.41    ( ! [X0] : (k1_zfmisc_1(X0) = k2_xboole_0(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0))) )),
% 0.19/0.41    inference(unit_resulting_resolution,[],[f98,f26])).
% 0.19/0.41  fof(f98,plain,(
% 0.19/0.41    ( ! [X0] : (r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(k1_xboole_0)),k1_zfmisc_1(X0))) )),
% 0.19/0.41    inference(superposition,[],[f25,f20])).
% 0.19/0.41  fof(f20,plain,(
% 0.19/0.41    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.41    inference(cnf_transformation,[],[f3])).
% 0.19/0.41  fof(f3,axiom,(
% 0.19/0.41    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.19/0.41  fof(f25,plain,(
% 0.19/0.41    ( ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))) )),
% 0.19/0.41    inference(cnf_transformation,[],[f9])).
% 0.19/0.41  fof(f9,axiom,(
% 0.19/0.41    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).
% 0.19/0.41  fof(f48,plain,(
% 0.19/0.41    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 0.19/0.41    inference(superposition,[],[f22,f23])).
% 0.19/0.41  fof(f85,plain,(
% 0.19/0.41    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl1_5),
% 0.19/0.41    inference(avatar_component_clause,[],[f83])).
% 0.19/0.41  fof(f83,plain,(
% 0.19/0.41    spl1_5 <=> m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.19/0.41  fof(f86,plain,(
% 0.19/0.41    ~spl1_5 | spl1_1 | ~spl1_2),
% 0.19/0.41    inference(avatar_split_clause,[],[f76,f40,f35,f83])).
% 0.19/0.41  fof(f35,plain,(
% 0.19/0.41    spl1_1 <=> m1_subset_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.19/0.41  fof(f40,plain,(
% 0.19/0.41    spl1_2 <=> k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.19/0.41    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.19/0.41  fof(f76,plain,(
% 0.19/0.41    ~m1_subset_1(k1_zfmisc_1(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | (spl1_1 | ~spl1_2)),
% 0.19/0.41    inference(backward_demodulation,[],[f37,f42])).
% 0.19/0.41  fof(f42,plain,(
% 0.19/0.41    k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl1_2),
% 0.19/0.41    inference(avatar_component_clause,[],[f40])).
% 0.19/0.41  fof(f37,plain,(
% 0.19/0.41    ~m1_subset_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl1_1),
% 0.19/0.41    inference(avatar_component_clause,[],[f35])).
% 0.19/0.41  fof(f43,plain,(
% 0.19/0.41    spl1_2),
% 0.19/0.41    inference(avatar_split_clause,[],[f33,f40])).
% 0.19/0.41  fof(f33,plain,(
% 0.19/0.41    k1_zfmisc_1(k1_xboole_0) = k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.19/0.41    inference(definition_unfolding,[],[f19,f31])).
% 0.19/0.41  fof(f31,plain,(
% 0.19/0.41    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.19/0.41    inference(definition_unfolding,[],[f21,f30])).
% 0.19/0.41  fof(f30,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.19/0.41    inference(definition_unfolding,[],[f24,f29])).
% 0.19/0.41  fof(f29,plain,(
% 0.19/0.41    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f7])).
% 0.19/0.41  fof(f7,axiom,(
% 0.19/0.41    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.19/0.41  fof(f24,plain,(
% 0.19/0.41    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f6])).
% 0.19/0.41  fof(f6,axiom,(
% 0.19/0.41    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.19/0.41  fof(f21,plain,(
% 0.19/0.41    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.41    inference(cnf_transformation,[],[f5])).
% 0.19/0.41  fof(f5,axiom,(
% 0.19/0.41    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.41  fof(f19,plain,(
% 0.19/0.41    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.19/0.41    inference(cnf_transformation,[],[f8])).
% 0.19/0.41  fof(f8,axiom,(
% 0.19/0.41    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.19/0.41  fof(f38,plain,(
% 0.19/0.41    ~spl1_1),
% 0.19/0.41    inference(avatar_split_clause,[],[f32,f35])).
% 0.19/0.41  fof(f32,plain,(
% 0.19/0.41    ~m1_subset_1(k2_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.41    inference(definition_unfolding,[],[f18,f31])).
% 0.19/0.41  fof(f18,plain,(
% 0.19/0.41    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.41    inference(cnf_transformation,[],[f16])).
% 0.19/0.41  fof(f16,plain,(
% 0.19/0.41    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f15])).
% 0.19/0.41  fof(f15,plain,(
% 0.19/0.41    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) => ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.19/0.41    introduced(choice_axiom,[])).
% 0.19/0.41  fof(f13,plain,(
% 0.19/0.41    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(ennf_transformation,[],[f12])).
% 0.19/0.41  fof(f12,negated_conjecture,(
% 0.19/0.41    ~! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.19/0.41    inference(negated_conjecture,[],[f11])).
% 0.19/0.41  fof(f11,conjecture,(
% 0.19/0.41    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.19/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
% 0.19/0.41  % SZS output end Proof for theBenchmark
% 0.19/0.41  % (21861)------------------------------
% 0.19/0.41  % (21861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.41  % (21861)Termination reason: Refutation
% 0.19/0.41  
% 0.19/0.41  % (21861)Memory used [KB]: 6268
% 0.19/0.41  % (21861)Time elapsed: 0.013 s
% 0.19/0.41  % (21861)------------------------------
% 0.19/0.41  % (21861)------------------------------
% 0.19/0.41  % (21854)Success in time 0.07 s
%------------------------------------------------------------------------------
