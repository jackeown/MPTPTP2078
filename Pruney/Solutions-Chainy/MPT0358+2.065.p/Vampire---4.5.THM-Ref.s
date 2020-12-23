%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:44:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  48 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 (  96 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f69,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f37,f48,f58])).

fof(f58,plain,
    ( spl2_2
    | ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl2_2
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f33,f47,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f47,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_3
  <=> r1_tarski(sK1,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f48,plain,
    ( spl2_2
    | spl2_3 ),
    inference(avatar_split_clause,[],[f25,f45,f31])).

fof(f25,plain,
    ( r1_tarski(sK1,k4_xboole_0(sK0,sK1))
    | k1_xboole_0 = sK1 ),
    inference(backward_demodulation,[],[f21,f23])).

fof(f23,plain,(
    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f13,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f13,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( r1_tarski(X1,k3_subset_1(X0,X1))
      <~> k1_subset_1(X0) = X1 )
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => ( r1_tarski(X1,k3_subset_1(X0,X1))
        <=> k1_subset_1(X0) = X1 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( r1_tarski(X1,k3_subset_1(X0,X1))
      <=> k1_subset_1(X0) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

fof(f21,plain,
    ( k1_xboole_0 = sK1
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f11,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

fof(f11,plain,
    ( sK1 = k1_subset_1(sK0)
    | r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f36])).

fof(f36,plain,
    ( $false
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f17,f29,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f29,plain,
    ( ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_1
  <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f17,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f34,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f22,f31,f27])).

fof(f22,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) ),
    inference(inner_rewriting,[],[f20])).

fof(f20,plain,
    ( k1_xboole_0 != sK1
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(definition_unfolding,[],[f12,f18])).

fof(f12,plain,
    ( sK1 != k1_subset_1(sK0)
    | ~ r1_tarski(sK1,k3_subset_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:38:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.47  % (11340)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.49  % (11340)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.49  % SZS output start Proof for theBenchmark
% 0.19/0.49  fof(f69,plain,(
% 0.19/0.49    $false),
% 0.19/0.49    inference(avatar_sat_refutation,[],[f34,f37,f48,f58])).
% 0.19/0.49  fof(f58,plain,(
% 0.19/0.49    spl2_2 | ~spl2_3),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f51])).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    $false | (spl2_2 | ~spl2_3)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f33,f47,f16])).
% 0.19/0.49  fof(f16,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.19/0.49    inference(cnf_transformation,[],[f9])).
% 0.19/0.49  fof(f9,plain,(
% 0.19/0.49    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | ~spl2_3),
% 0.19/0.49    inference(avatar_component_clause,[],[f45])).
% 0.19/0.49  fof(f45,plain,(
% 0.19/0.49    spl2_3 <=> r1_tarski(sK1,k4_xboole_0(sK0,sK1))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.19/0.49  fof(f33,plain,(
% 0.19/0.49    k1_xboole_0 != sK1 | spl2_2),
% 0.19/0.49    inference(avatar_component_clause,[],[f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    spl2_2 <=> k1_xboole_0 = sK1),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    spl2_2 | spl2_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f25,f45,f31])).
% 0.19/0.49  fof(f25,plain,(
% 0.19/0.49    r1_tarski(sK1,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = sK1),
% 0.19/0.49    inference(backward_demodulation,[],[f21,f23])).
% 0.19/0.49  fof(f23,plain,(
% 0.19/0.49    k3_subset_1(sK0,sK1) = k4_xboole_0(sK0,sK1)),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f13,f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,plain,(
% 0.19/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 0.19/0.49  fof(f13,plain,(
% 0.19/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.19/0.49    inference(cnf_transformation,[],[f8])).
% 0.19/0.49  fof(f8,plain,(
% 0.19/0.49    ? [X0,X1] : ((r1_tarski(X1,k3_subset_1(X0,X1)) <~> k1_subset_1(X0) = X1) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f7])).
% 0.19/0.49  fof(f7,negated_conjecture,(
% 0.19/0.49    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.19/0.49    inference(negated_conjecture,[],[f6])).
% 0.19/0.49  fof(f6,conjecture,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (r1_tarski(X1,k3_subset_1(X0,X1)) <=> k1_subset_1(X0) = X1))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    k1_xboole_0 = sK1 | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.49    inference(definition_unfolding,[],[f11,f18])).
% 0.19/0.49  fof(f18,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f4])).
% 0.19/0.49  fof(f4,axiom,(
% 0.19/0.49    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    sK1 = k1_subset_1(sK0) | r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.49    inference(cnf_transformation,[],[f8])).
% 0.19/0.49  fof(f37,plain,(
% 0.19/0.49    spl2_1),
% 0.19/0.49    inference(avatar_contradiction_clause,[],[f36])).
% 0.19/0.49  fof(f36,plain,(
% 0.19/0.49    $false | spl2_1),
% 0.19/0.49    inference(unit_resulting_resolution,[],[f17,f29,f15])).
% 0.19/0.49  fof(f15,plain,(
% 0.19/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f1])).
% 0.19/0.49  fof(f1,axiom,(
% 0.19/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0)) | spl2_1),
% 0.19/0.49    inference(avatar_component_clause,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    spl2_1 <=> r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.19/0.49  fof(f17,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f3])).
% 0.19/0.49  fof(f3,axiom,(
% 0.19/0.49    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.19/0.49  fof(f34,plain,(
% 0.19/0.49    ~spl2_1 | ~spl2_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f22,f31,f27])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    k1_xboole_0 != sK1 | ~r1_tarski(k1_xboole_0,k3_subset_1(sK0,k1_xboole_0))),
% 0.19/0.49    inference(inner_rewriting,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    k1_xboole_0 != sK1 | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.49    inference(definition_unfolding,[],[f12,f18])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    sK1 != k1_subset_1(sK0) | ~r1_tarski(sK1,k3_subset_1(sK0,sK1))),
% 0.19/0.49    inference(cnf_transformation,[],[f8])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (11340)------------------------------
% 0.19/0.49  % (11340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (11340)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (11340)Memory used [KB]: 6140
% 0.19/0.49  % (11340)Time elapsed: 0.111 s
% 0.19/0.49  % (11340)------------------------------
% 0.19/0.49  % (11340)------------------------------
% 0.19/0.50  % (11335)Success in time 0.15 s
%------------------------------------------------------------------------------
