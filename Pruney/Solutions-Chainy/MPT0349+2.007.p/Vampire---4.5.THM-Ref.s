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
% DateTime   : Thu Dec  3 12:43:49 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 117 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :   18
%              Number of atoms          :   86 ( 134 expanded)
%              Number of equality atoms :   65 ( 110 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f74,f125])).

fof(f125,plain,(
    spl1_2 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl1_2 ),
    inference(unit_resulting_resolution,[],[f73,f118])).

fof(f118,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f117,f91])).

fof(f91,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f84,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f75,f31])).

fof(f31,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f44,f31])).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f117,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f115,f60])).

fof(f60,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f33,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f115,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f61,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ) ),
    inference(forward_demodulation,[],[f113,f97])).

fof(f97,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f75,f91])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(forward_demodulation,[],[f63,f44])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f40,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f61,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f35,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).

fof(f73,plain,
    ( sK0 != k3_subset_1(sK0,k1_xboole_0)
    | spl1_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl1_2
  <=> sK0 = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f74,plain,
    ( ~ spl1_2
    | spl1_1 ),
    inference(avatar_split_clause,[],[f69,f65,f71])).

fof(f65,plain,
    ( spl1_1
  <=> k2_subset_1(sK0) = k3_subset_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f69,plain,
    ( sK0 != k3_subset_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(backward_demodulation,[],[f67,f30])).

fof(f30,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f67,plain,
    ( k2_subset_1(sK0) != k3_subset_1(sK0,k1_xboole_0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f68,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f58,f65])).

fof(f58,plain,(
    k2_subset_1(sK0) != k3_subset_1(sK0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f28,plain,(
    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f26])).

fof(f26,plain,
    ( ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0))
   => k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:23:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (7423)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.43  % (7423)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f68,f74,f125])).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    spl1_2),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f121])).
% 0.20/0.43  fof(f121,plain,(
% 0.20/0.43    $false | spl1_2),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f73,f118])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(forward_demodulation,[],[f117,f91])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.43    inference(forward_demodulation,[],[f84,f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.20/0.43    inference(superposition,[],[f75,f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 0.20/0.43    inference(superposition,[],[f44,f31])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(forward_demodulation,[],[f115,f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f33,f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f38,f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f39,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f43,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f45,f50])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f46,f49])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f47,f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,axiom,(
% 0.20/0.43    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))) )),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f61,f114])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f113,f97])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.20/0.43    inference(backward_demodulation,[],[f75,f91])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f63,f44])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f42,f56])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f40,f55])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f41,f54])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f35,f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,axiom,(
% 0.20/0.43    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,axiom,(
% 0.20/0.43    ! [X0] : m1_subset_1(k1_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_subset_1)).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    sK0 != k3_subset_1(sK0,k1_xboole_0) | spl1_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f71])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl1_2 <=> sK0 = k3_subset_1(sK0,k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    ~spl1_2 | spl1_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f69,f65,f71])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    spl1_1 <=> k2_subset_1(sK0) = k3_subset_1(sK0,k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    sK0 != k3_subset_1(sK0,k1_xboole_0) | spl1_1),
% 0.20/0.43    inference(backward_demodulation,[],[f67,f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,axiom,(
% 0.20/0.43    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.43  fof(f67,plain,(
% 0.20/0.43    k2_subset_1(sK0) != k3_subset_1(sK0,k1_xboole_0) | spl1_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f65])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    ~spl1_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f58,f65])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    k2_subset_1(sK0) != k3_subset_1(sK0,k1_xboole_0)),
% 0.20/0.43    inference(definition_unfolding,[],[f28,f29])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0)) => k2_subset_1(sK0) != k3_subset_1(sK0,k1_subset_1(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ? [X0] : k2_subset_1(X0) != k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f22])).
% 0.20/0.43  fof(f22,negated_conjecture,(
% 0.20/0.43    ~! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.43    inference(negated_conjecture,[],[f21])).
% 0.20/0.43  fof(f21,conjecture,(
% 0.20/0.43    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (7423)------------------------------
% 0.20/0.43  % (7423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (7423)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (7423)Memory used [KB]: 6140
% 0.20/0.43  % (7423)Time elapsed: 0.007 s
% 0.20/0.43  % (7423)------------------------------
% 0.20/0.43  % (7423)------------------------------
% 0.20/0.43  % (7416)Success in time 0.072 s
%------------------------------------------------------------------------------
