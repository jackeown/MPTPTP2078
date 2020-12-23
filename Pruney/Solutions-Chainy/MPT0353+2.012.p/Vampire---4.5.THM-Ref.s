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
% DateTime   : Thu Dec  3 12:44:22 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 195 expanded)
%              Number of leaves         :   19 (  63 expanded)
%              Depth                    :   15
%              Number of atoms          :  137 ( 400 expanded)
%              Number of equality atoms :   62 ( 168 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2171,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f2160])).

fof(f2160,plain,(
    k6_subset_1(sK1,sK2) != k6_subset_1(sK1,sK2) ),
    inference(superposition,[],[f771,f1886])).

fof(f1886,plain,(
    ! [X1] : k6_subset_1(sK1,X1) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1)) ),
    inference(superposition,[],[f803,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f803,plain,(
    ! [X0] : k6_subset_1(sK1,X0) = k3_xboole_0(k5_xboole_0(sK0,X0),sK1) ),
    inference(forward_demodulation,[],[f793,f72])).

fof(f72,plain,(
    ! [X2,X1] : k6_subset_1(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f58,f45])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1) ),
    inference(definition_unfolding,[],[f46,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f793,plain,(
    ! [X0] : k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(superposition,[],[f52,f659])).

fof(f659,plain,(
    sK1 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f656,f45])).

fof(f656,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f654,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f654,plain,(
    r1_tarski(sK1,sK0) ),
    inference(subsumption_resolution,[],[f649,f125])).

fof(f125,plain,(
    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f43,f93])).

fof(f93,plain,(
    k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1) ),
    inference(resolution,[],[f59,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f30,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
            & m1_subset_1(X2,k1_zfmisc_1(X0)) )
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( ? [X2] :
          ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2))
        & m1_subset_1(X2,k1_zfmisc_1(sK0)) )
   => ( k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))
      & m1_subset_1(sK2,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          & m1_subset_1(X2,k1_zfmisc_1(X0)) )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ! [X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(X0))
           => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k6_subset_1(X0,X1) ) ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f43,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f649,plain,
    ( r1_tarski(sK1,sK0)
    | ~ m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f612,f84])).

fof(f84,plain,(
    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1)) ),
    inference(resolution,[],[f49,f33])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f612,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f611,f39])).

fof(f39,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f611,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(subsumption_resolution,[],[f602,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f602,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X1),X0)
      | ~ r1_tarski(k1_xboole_0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f50,f56])).

fof(f56,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f55,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f41,f37])).

fof(f37,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

fof(f38,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r1_tarski(X1,X2)
              | ~ r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
            & ( r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))
              | ~ r1_tarski(X1,X2) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_tarski(X1,X2)
          <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f771,plain,(
    k6_subset_1(sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2)) ),
    inference(backward_demodulation,[],[f216,f765])).

fof(f765,plain,(
    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(backward_demodulation,[],[f94,f732])).

fof(f732,plain,(
    k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f72,f657])).

fof(f657,plain,(
    sK2 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f655,f47])).

fof(f655,plain,(
    r1_tarski(sK2,sK0) ),
    inference(subsumption_resolution,[],[f650,f130])).

fof(f130,plain,(
    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f43,f94])).

fof(f650,plain,
    ( r1_tarski(sK2,sK0)
    | ~ m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0)) ),
    inference(superposition,[],[f612,f85])).

fof(f85,plain,(
    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f49,f34])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2) ),
    inference(resolution,[],[f59,f34])).

fof(f216,plain,(
    k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2) ),
    inference(backward_demodulation,[],[f139,f208])).

fof(f208,plain,(
    ! [X0] : k7_subset_1(sK0,sK1,X0) = k6_subset_1(sK1,X0) ),
    inference(resolution,[],[f60,f33])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2) ) ),
    inference(definition_unfolding,[],[f53,f44])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f139,plain,(
    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) ),
    inference(superposition,[],[f35,f131])).

fof(f131,plain,(
    ! [X0] : k9_subset_1(sK0,X0,k3_subset_1(sK0,sK2)) = k3_xboole_0(X0,k3_subset_1(sK0,sK2)) ),
    inference(resolution,[],[f130,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f35,plain,(
    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:50:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.44  % (1900)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.47  % (1889)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (1887)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (1894)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (1891)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (1885)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (1895)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (1893)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (1884)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.51  % (1886)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (1892)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.51  % (1897)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.52  % (1888)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.52  % (1899)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.52  % (1890)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 1.31/0.53  % (1898)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.31/0.53  % (1896)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 1.31/0.54  % (1901)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.45/0.56  % (1893)Refutation found. Thanks to Tanya!
% 1.45/0.56  % SZS status Theorem for theBenchmark
% 1.45/0.56  % SZS output start Proof for theBenchmark
% 1.45/0.56  fof(f2171,plain,(
% 1.45/0.56    $false),
% 1.45/0.56    inference(trivial_inequality_removal,[],[f2160])).
% 1.45/0.56  fof(f2160,plain,(
% 1.45/0.56    k6_subset_1(sK1,sK2) != k6_subset_1(sK1,sK2)),
% 1.45/0.56    inference(superposition,[],[f771,f1886])).
% 1.45/0.56  fof(f1886,plain,(
% 1.45/0.56    ( ! [X1] : (k6_subset_1(sK1,X1) = k3_xboole_0(sK1,k5_xboole_0(sK0,X1))) )),
% 1.45/0.56    inference(superposition,[],[f803,f45])).
% 1.45/0.56  fof(f45,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f1])).
% 1.45/0.56  fof(f1,axiom,(
% 1.45/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.45/0.56  fof(f803,plain,(
% 1.45/0.56    ( ! [X0] : (k6_subset_1(sK1,X0) = k3_xboole_0(k5_xboole_0(sK0,X0),sK1)) )),
% 1.45/0.56    inference(forward_demodulation,[],[f793,f72])).
% 1.45/0.56  fof(f72,plain,(
% 1.45/0.56    ( ! [X2,X1] : (k6_subset_1(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 1.45/0.56    inference(superposition,[],[f58,f45])).
% 1.45/0.56  fof(f58,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,X1)) = k6_subset_1(X0,X1)) )),
% 1.45/0.56    inference(definition_unfolding,[],[f46,f44])).
% 1.45/0.56  fof(f44,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f13])).
% 1.45/0.56  fof(f13,axiom,(
% 1.45/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 1.45/0.56  fof(f46,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f3])).
% 1.45/0.56  fof(f3,axiom,(
% 1.45/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.45/0.56  fof(f793,plain,(
% 1.45/0.56    ( ! [X0] : (k3_xboole_0(k5_xboole_0(sK0,X0),sK1) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) )),
% 1.45/0.56    inference(superposition,[],[f52,f659])).
% 1.45/0.56  fof(f659,plain,(
% 1.45/0.56    sK1 = k3_xboole_0(sK0,sK1)),
% 1.45/0.56    inference(superposition,[],[f656,f45])).
% 1.45/0.56  fof(f656,plain,(
% 1.45/0.56    sK1 = k3_xboole_0(sK1,sK0)),
% 1.45/0.56    inference(resolution,[],[f654,f47])).
% 1.45/0.56  fof(f47,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.45/0.56    inference(cnf_transformation,[],[f23])).
% 1.45/0.56  fof(f23,plain,(
% 1.45/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.45/0.56    inference(ennf_transformation,[],[f5])).
% 1.45/0.56  fof(f5,axiom,(
% 1.45/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.45/0.56  fof(f654,plain,(
% 1.45/0.56    r1_tarski(sK1,sK0)),
% 1.45/0.56    inference(subsumption_resolution,[],[f649,f125])).
% 1.45/0.56  fof(f125,plain,(
% 1.45/0.56    m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.45/0.56    inference(superposition,[],[f43,f93])).
% 1.45/0.56  fof(f93,plain,(
% 1.45/0.56    k3_subset_1(sK0,sK1) = k6_subset_1(sK0,sK1)),
% 1.45/0.56    inference(resolution,[],[f59,f33])).
% 1.45/0.56  fof(f33,plain,(
% 1.45/0.56    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.45/0.56    inference(cnf_transformation,[],[f31])).
% 1.45/0.56  fof(f31,plain,(
% 1.45/0.56    (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 1.45/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f30,f29])).
% 1.45/0.56  fof(f29,plain,(
% 1.45/0.56    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f30,plain,(
% 1.45/0.56    ? [X2] : (k7_subset_1(sK0,sK1,X2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,X2)) & m1_subset_1(X2,k1_zfmisc_1(sK0))) => (k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f22,plain,(
% 1.45/0.56    ? [X0,X1] : (? [X2] : (k7_subset_1(X0,X1,X2) != k9_subset_1(X0,X1,k3_subset_1(X0,X2)) & m1_subset_1(X2,k1_zfmisc_1(X0))) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f20])).
% 1.45/0.56  fof(f20,negated_conjecture,(
% 1.45/0.56    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.45/0.56    inference(negated_conjecture,[],[f19])).
% 1.45/0.56  fof(f19,conjecture,(
% 1.45/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 1.45/0.56  fof(f59,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,X1) = k6_subset_1(X0,X1)) )),
% 1.45/0.56    inference(definition_unfolding,[],[f48,f44])).
% 1.45/0.56  fof(f48,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f24])).
% 1.45/0.56  fof(f24,plain,(
% 1.45/0.56    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f9])).
% 1.45/0.56  fof(f9,axiom,(
% 1.45/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 1.45/0.56  fof(f43,plain,(
% 1.45/0.56    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f11])).
% 1.45/0.56  fof(f11,axiom,(
% 1.45/0.56    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 1.45/0.56  fof(f649,plain,(
% 1.45/0.56    r1_tarski(sK1,sK0) | ~m1_subset_1(k3_subset_1(sK0,sK1),k1_zfmisc_1(sK0))),
% 1.45/0.56    inference(superposition,[],[f612,f84])).
% 1.45/0.56  fof(f84,plain,(
% 1.45/0.56    sK1 = k3_subset_1(sK0,k3_subset_1(sK0,sK1))),
% 1.45/0.56    inference(resolution,[],[f49,f33])).
% 1.45/0.56  fof(f49,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 1.45/0.56    inference(cnf_transformation,[],[f25])).
% 1.45/0.56  fof(f25,plain,(
% 1.45/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f12])).
% 1.45/0.56  fof(f12,axiom,(
% 1.45/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.45/0.56  fof(f612,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(subsumption_resolution,[],[f611,f39])).
% 1.45/0.56  fof(f39,plain,(
% 1.45/0.56    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f18])).
% 1.45/0.56  fof(f18,axiom,(
% 1.45/0.56    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 1.45/0.56  fof(f611,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(subsumption_resolution,[],[f602,f36])).
% 1.45/0.56  fof(f36,plain,(
% 1.45/0.56    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f6])).
% 1.45/0.56  fof(f6,axiom,(
% 1.45/0.56    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.45/0.56  fof(f602,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r1_tarski(k3_subset_1(X0,X1),X0) | ~r1_tarski(k1_xboole_0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(superposition,[],[f50,f56])).
% 1.45/0.56  fof(f56,plain,(
% 1.45/0.56    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 1.45/0.56    inference(definition_unfolding,[],[f38,f55])).
% 1.45/0.56  fof(f55,plain,(
% 1.45/0.56    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 1.45/0.56    inference(definition_unfolding,[],[f41,f37])).
% 1.45/0.56  fof(f37,plain,(
% 1.45/0.56    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f7])).
% 1.45/0.56  fof(f7,axiom,(
% 1.45/0.56    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 1.45/0.56  fof(f41,plain,(
% 1.45/0.56    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f16])).
% 1.45/0.56  fof(f16,axiom,(
% 1.45/0.56    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).
% 1.45/0.56  fof(f38,plain,(
% 1.45/0.56    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.45/0.56    inference(cnf_transformation,[],[f8])).
% 1.45/0.56  fof(f8,axiom,(
% 1.45/0.56    ! [X0] : k2_subset_1(X0) = X0),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.45/0.56  fof(f50,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f32])).
% 1.45/0.56  fof(f32,plain,(
% 1.45/0.56    ! [X0,X1] : (! [X2] : (((r1_tarski(X1,X2) | ~r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) & (r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)) | ~r1_tarski(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.56    inference(nnf_transformation,[],[f26])).
% 1.45/0.56  fof(f26,plain,(
% 1.45/0.56    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f17])).
% 1.45/0.56  fof(f17,axiom,(
% 1.45/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_tarski(X1,X2) <=> r1_tarski(k3_subset_1(X0,X2),k3_subset_1(X0,X1)))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).
% 1.45/0.56  fof(f52,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f4])).
% 1.45/0.56  fof(f4,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.45/0.56  fof(f771,plain,(
% 1.45/0.56    k6_subset_1(sK1,sK2) != k3_xboole_0(sK1,k5_xboole_0(sK0,sK2))),
% 1.45/0.56    inference(backward_demodulation,[],[f216,f765])).
% 1.45/0.56  fof(f765,plain,(
% 1.45/0.56    k3_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 1.45/0.56    inference(backward_demodulation,[],[f94,f732])).
% 1.45/0.56  fof(f732,plain,(
% 1.45/0.56    k6_subset_1(sK0,sK2) = k5_xboole_0(sK0,sK2)),
% 1.45/0.56    inference(superposition,[],[f72,f657])).
% 1.45/0.56  fof(f657,plain,(
% 1.45/0.56    sK2 = k3_xboole_0(sK2,sK0)),
% 1.45/0.56    inference(resolution,[],[f655,f47])).
% 1.45/0.56  fof(f655,plain,(
% 1.45/0.56    r1_tarski(sK2,sK0)),
% 1.45/0.56    inference(subsumption_resolution,[],[f650,f130])).
% 1.45/0.56  fof(f130,plain,(
% 1.45/0.56    m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.45/0.56    inference(superposition,[],[f43,f94])).
% 1.45/0.56  fof(f650,plain,(
% 1.45/0.56    r1_tarski(sK2,sK0) | ~m1_subset_1(k3_subset_1(sK0,sK2),k1_zfmisc_1(sK0))),
% 1.45/0.56    inference(superposition,[],[f612,f85])).
% 1.45/0.56  fof(f85,plain,(
% 1.45/0.56    sK2 = k3_subset_1(sK0,k3_subset_1(sK0,sK2))),
% 1.45/0.56    inference(resolution,[],[f49,f34])).
% 1.45/0.56  fof(f34,plain,(
% 1.45/0.56    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.45/0.56    inference(cnf_transformation,[],[f31])).
% 1.45/0.56  fof(f94,plain,(
% 1.45/0.56    k3_subset_1(sK0,sK2) = k6_subset_1(sK0,sK2)),
% 1.45/0.56    inference(resolution,[],[f59,f34])).
% 1.45/0.56  fof(f216,plain,(
% 1.45/0.56    k3_xboole_0(sK1,k3_subset_1(sK0,sK2)) != k6_subset_1(sK1,sK2)),
% 1.45/0.56    inference(backward_demodulation,[],[f139,f208])).
% 1.45/0.56  fof(f208,plain,(
% 1.45/0.56    ( ! [X0] : (k7_subset_1(sK0,sK1,X0) = k6_subset_1(sK1,X0)) )),
% 1.45/0.56    inference(resolution,[],[f60,f33])).
% 1.45/0.56  fof(f60,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k6_subset_1(X1,X2)) )),
% 1.45/0.56    inference(definition_unfolding,[],[f53,f44])).
% 1.45/0.56  fof(f53,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f27])).
% 1.45/0.56  fof(f27,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f14])).
% 1.45/0.56  fof(f14,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 1.45/0.56  fof(f139,plain,(
% 1.45/0.56    k7_subset_1(sK0,sK1,sK2) != k3_xboole_0(sK1,k3_subset_1(sK0,sK2))),
% 1.45/0.56    inference(superposition,[],[f35,f131])).
% 1.45/0.56  fof(f131,plain,(
% 1.45/0.56    ( ! [X0] : (k9_subset_1(sK0,X0,k3_subset_1(sK0,sK2)) = k3_xboole_0(X0,k3_subset_1(sK0,sK2))) )),
% 1.45/0.56    inference(resolution,[],[f130,f54])).
% 1.45/0.56  fof(f54,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f28])).
% 1.45/0.56  fof(f28,plain,(
% 1.45/0.56    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.45/0.56    inference(ennf_transformation,[],[f15])).
% 1.45/0.56  fof(f15,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.45/0.56  fof(f35,plain,(
% 1.45/0.56    k7_subset_1(sK0,sK1,sK2) != k9_subset_1(sK0,sK1,k3_subset_1(sK0,sK2))),
% 1.45/0.56    inference(cnf_transformation,[],[f31])).
% 1.45/0.56  % SZS output end Proof for theBenchmark
% 1.45/0.56  % (1893)------------------------------
% 1.45/0.56  % (1893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (1893)Termination reason: Refutation
% 1.45/0.56  
% 1.45/0.56  % (1893)Memory used [KB]: 11769
% 1.45/0.56  % (1893)Time elapsed: 0.141 s
% 1.45/0.56  % (1893)------------------------------
% 1.45/0.56  % (1893)------------------------------
% 1.45/0.57  % (1883)Success in time 0.199 s
%------------------------------------------------------------------------------
