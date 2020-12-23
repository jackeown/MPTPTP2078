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
% DateTime   : Thu Dec  3 12:42:23 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   43 (  86 expanded)
%              Number of leaves         :    8 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  125 ( 243 expanded)
%              Number of equality atoms :  105 ( 221 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f159,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f153,f158])).

fof(f158,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f157])).

fof(f157,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f156,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
    & k1_xboole_0 != sK0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f18])).

fof(f18,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) )
      & k1_xboole_0 != sK0 ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f156,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f155,f150])).

fof(f150,plain,(
    ! [X1] : k1_xboole_0 != k2_tarski(X1,X1) ),
    inference(forward_demodulation,[],[f59,f60])).

fof(f60,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X2) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f59,plain,(
    ! [X1] : k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)) ) ),
    inference(definition_unfolding,[],[f38,f30,f30,f30])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f155,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = sK0
    | ~ spl3_1 ),
    inference(trivial_inequality_removal,[],[f154])).

fof(f154,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k2_tarski(sK1,sK1)
    | k1_xboole_0 = sK0
    | ~ spl3_1 ),
    inference(superposition,[],[f35,f67])).

fof(f67,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_1
  <=> k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f153,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f152])).

fof(f152,plain,
    ( $false
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f151])).

fof(f151,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_2 ),
    inference(superposition,[],[f150,f78])).

fof(f78,plain,
    ( k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f77,f27])).

fof(f77,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f74])).

fof(f74,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k2_tarski(sK1,sK1)
    | ~ spl3_2 ),
    inference(superposition,[],[f35,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f72,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f46,f69,f65])).

fof(f46,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1))
    | k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0) ),
    inference(definition_unfolding,[],[f28,f30,f30])).

fof(f28,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:11:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (3063)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.49  % (3047)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.49  % (3047)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f72,f153,f158])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    ~spl3_1),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f157])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    $false | ~spl3_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f156,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    k1_xboole_0 != sK0),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    (k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)) & k1_xboole_0 != sK0)),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.20/0.49    inference(negated_conjecture,[],[f10])).
% 0.20/0.49  fof(f10,conjecture,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.20/0.49  fof(f156,plain,(
% 0.20/0.49    k1_xboole_0 = sK0 | ~spl3_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f155,f150])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ( ! [X1] : (k1_xboole_0 != k2_tarski(X1,X1)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f59,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 0.20/0.49    inference(equality_resolution,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X2) != X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 0.20/0.49    inference(nnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X1] : (k2_tarski(X1,X1) != k4_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0,X1] : (X0 != X1 | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f38,f30,f30,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.20/0.49    inference(nnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    k1_xboole_0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0 | ~spl3_1),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f154])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k2_tarski(sK1,sK1) | k1_xboole_0 = sK0 | ~spl3_1),
% 0.20/0.49    inference(superposition,[],[f35,f67])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f65])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    spl3_1 <=> k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ~spl3_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f152])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    $false | ~spl3_2),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f151])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | ~spl3_2),
% 0.20/0.49    inference(superposition,[],[f150,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl3_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f77,f27])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    k1_xboole_0 = sK0 | k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl3_2),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k2_tarski(sK1,sK1) | ~spl3_2),
% 0.20/0.49    inference(superposition,[],[f35,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1)) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl3_2 <=> k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl3_1 | spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f46,f69,f65])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    k1_xboole_0 = k2_zfmisc_1(sK0,k2_tarski(sK1,sK1)) | k1_xboole_0 = k2_zfmisc_1(k2_tarski(sK1,sK1),sK0)),
% 0.20/0.49    inference(definition_unfolding,[],[f28,f30,f30])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    k1_xboole_0 = k2_zfmisc_1(sK0,k1_tarski(sK1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK1),sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (3047)------------------------------
% 0.20/0.49  % (3047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (3047)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (3047)Memory used [KB]: 10746
% 0.20/0.49  % (3047)Time elapsed: 0.094 s
% 0.20/0.49  % (3047)------------------------------
% 0.20/0.49  % (3047)------------------------------
% 0.20/0.49  % (3043)Success in time 0.14 s
%------------------------------------------------------------------------------
