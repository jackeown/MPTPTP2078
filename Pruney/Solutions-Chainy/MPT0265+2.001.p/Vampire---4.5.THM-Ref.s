%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:26 EST 2020

% Result     : Theorem 1.20s
% Output     : Refutation 1.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  82 expanded)
%              Number of leaves         :   11 (  25 expanded)
%              Depth                    :   14
%              Number of atoms          :  112 ( 239 expanded)
%              Number of equality atoms :   58 ( 122 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f136,f159])).

fof(f159,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f157,f41])).

fof(f41,plain,(
    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f18,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

% (21868)Termination reason: Refutation not found, incomplete strategy

% (21868)Memory used [KB]: 10746
fof(f12,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

% (21868)Time elapsed: 0.105 s
% (21868)------------------------------
% (21868)------------------------------
fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f18,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    & ( sK0 = sK2
      | ~ r2_hidden(sK2,sK1) )
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
        & ( X0 = X2
          | ~ r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) )
   => ( k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
      & ( sK0 = sK2
        | ~ r2_hidden(sK2,sK1) )
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f157,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f144,f23])).

fof(f23,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f144,plain,
    ( k1_tarski(sK0) != k3_xboole_0(sK1,k2_tarski(sK0,sK0))
    | ~ spl3_2 ),
    inference(superposition,[],[f48,f39])).

fof(f39,plain,
    ( sK0 = sK2
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f48,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k2_tarski(sK0,sK2)) ),
    inference(superposition,[],[f20,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f20,plain,(
    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f136,plain,
    ( spl3_2
    | spl3_1 ),
    inference(avatar_split_clause,[],[f135,f33,f37])).

fof(f33,plain,
    ( spl3_1
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f135,plain,
    ( sK0 = sK2
    | spl3_1 ),
    inference(subsumption_resolution,[],[f118,f48])).

fof(f118,plain,
    ( k1_tarski(sK0) = k3_xboole_0(sK1,k2_tarski(sK0,sK2))
    | sK0 = sK2
    | spl3_1 ),
    inference(superposition,[],[f29,f77])).

fof(f77,plain,
    ( k3_xboole_0(sK1,k2_tarski(sK0,sK2)) = k4_xboole_0(k2_tarski(sK0,sK2),k1_tarski(sK2))
    | spl3_1 ),
    inference(forward_demodulation,[],[f76,f21])).

fof(f76,plain,
    ( k3_xboole_0(k2_tarski(sK0,sK2),sK1) = k4_xboole_0(k2_tarski(sK0,sK2),k1_tarski(sK2))
    | spl3_1 ),
    inference(superposition,[],[f30,f70])).

fof(f70,plain,
    ( k1_tarski(sK2) = k4_xboole_0(k2_tarski(sK0,sK2),sK1)
    | spl3_1 ),
    inference(forward_demodulation,[],[f69,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f69,plain,
    ( k1_tarski(sK2) = k4_xboole_0(k2_tarski(sK2,sK0),sK1)
    | spl3_1 ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f43,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK1)
      | k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,sK0),sK1) ) ),
    inference(resolution,[],[f18,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | ( X0 != X1
          & ~ r2_hidden(X1,X2) )
        | r2_hidden(X0,X2) )
      & ( ( ( X0 = X1
            | r2_hidden(X1,X2) )
          & ~ r2_hidden(X0,X2) )
        | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 != X1
     => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).

fof(f40,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f19,f37,f33])).

fof(f19,plain,
    ( sK0 = sK2
    | ~ r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:10:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (21870)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (21868)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.20/0.51  % (21870)Refutation found. Thanks to Tanya!
% 1.20/0.51  % SZS status Theorem for theBenchmark
% 1.20/0.52  % (21868)Refutation not found, incomplete strategy% (21868)------------------------------
% 1.20/0.52  % (21868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % SZS output start Proof for theBenchmark
% 1.20/0.52  fof(f165,plain,(
% 1.20/0.52    $false),
% 1.20/0.52    inference(avatar_sat_refutation,[],[f40,f136,f159])).
% 1.20/0.52  fof(f159,plain,(
% 1.20/0.52    ~spl3_2),
% 1.20/0.52    inference(avatar_contradiction_clause,[],[f158])).
% 1.20/0.52  fof(f158,plain,(
% 1.20/0.52    $false | ~spl3_2),
% 1.20/0.52    inference(subsumption_resolution,[],[f157,f41])).
% 1.20/0.52  fof(f41,plain,(
% 1.20/0.52    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 1.20/0.52    inference(resolution,[],[f18,f28])).
% 1.20/0.52  fof(f28,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f12])).
% 1.20/0.52  % (21868)Termination reason: Refutation not found, incomplete strategy
% 1.20/0.52  
% 1.20/0.52  % (21868)Memory used [KB]: 10746
% 1.20/0.52  fof(f12,plain,(
% 1.20/0.52    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f5])).
% 1.20/0.52  % (21868)Time elapsed: 0.105 s
% 1.20/0.52  % (21868)------------------------------
% 1.20/0.52  % (21868)------------------------------
% 1.20/0.52  fof(f5,axiom,(
% 1.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.20/0.52  fof(f18,plain,(
% 1.20/0.52    r2_hidden(sK0,sK1)),
% 1.20/0.52    inference(cnf_transformation,[],[f15])).
% 1.20/0.52  fof(f15,plain,(
% 1.20/0.52    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & (sK0 = sK2 | ~r2_hidden(sK2,sK1)) & r2_hidden(sK0,sK1)),
% 1.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f14])).
% 1.20/0.52  fof(f14,plain,(
% 1.20/0.52    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1)) => (k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & (sK0 = sK2 | ~r2_hidden(sK2,sK1)) & r2_hidden(sK0,sK1))),
% 1.20/0.52    introduced(choice_axiom,[])).
% 1.20/0.52  fof(f11,plain,(
% 1.20/0.52    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 1.20/0.52    inference(flattening,[],[f10])).
% 1.20/0.52  fof(f10,plain,(
% 1.20/0.52    ? [X0,X1,X2] : ((k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 1.20/0.52    inference(ennf_transformation,[],[f9])).
% 1.20/0.52  fof(f9,negated_conjecture,(
% 1.20/0.52    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 1.20/0.52    inference(negated_conjecture,[],[f8])).
% 1.20/0.52  fof(f8,conjecture,(
% 1.20/0.52    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 1.20/0.52  fof(f157,plain,(
% 1.20/0.52    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) | ~spl3_2),
% 1.20/0.52    inference(forward_demodulation,[],[f144,f23])).
% 1.20/0.52  fof(f23,plain,(
% 1.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f4])).
% 1.20/0.52  fof(f4,axiom,(
% 1.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.20/0.52  fof(f144,plain,(
% 1.20/0.52    k1_tarski(sK0) != k3_xboole_0(sK1,k2_tarski(sK0,sK0)) | ~spl3_2),
% 1.20/0.52    inference(superposition,[],[f48,f39])).
% 1.20/0.52  fof(f39,plain,(
% 1.20/0.52    sK0 = sK2 | ~spl3_2),
% 1.20/0.52    inference(avatar_component_clause,[],[f37])).
% 1.20/0.52  fof(f37,plain,(
% 1.20/0.52    spl3_2 <=> sK0 = sK2),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.20/0.52  fof(f48,plain,(
% 1.20/0.52    k1_tarski(sK0) != k3_xboole_0(sK1,k2_tarski(sK0,sK2))),
% 1.20/0.52    inference(superposition,[],[f20,f21])).
% 1.20/0.52  fof(f21,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f1])).
% 1.20/0.52  fof(f1,axiom,(
% 1.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.20/0.52  fof(f20,plain,(
% 1.20/0.52    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 1.20/0.52    inference(cnf_transformation,[],[f15])).
% 1.20/0.52  fof(f136,plain,(
% 1.20/0.52    spl3_2 | spl3_1),
% 1.20/0.52    inference(avatar_split_clause,[],[f135,f33,f37])).
% 1.20/0.52  fof(f33,plain,(
% 1.20/0.52    spl3_1 <=> r2_hidden(sK2,sK1)),
% 1.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.20/0.52  fof(f135,plain,(
% 1.20/0.52    sK0 = sK2 | spl3_1),
% 1.20/0.52    inference(subsumption_resolution,[],[f118,f48])).
% 1.20/0.52  fof(f118,plain,(
% 1.20/0.52    k1_tarski(sK0) = k3_xboole_0(sK1,k2_tarski(sK0,sK2)) | sK0 = sK2 | spl3_1),
% 1.20/0.52    inference(superposition,[],[f29,f77])).
% 1.20/0.52  fof(f77,plain,(
% 1.20/0.52    k3_xboole_0(sK1,k2_tarski(sK0,sK2)) = k4_xboole_0(k2_tarski(sK0,sK2),k1_tarski(sK2)) | spl3_1),
% 1.20/0.52    inference(forward_demodulation,[],[f76,f21])).
% 1.20/0.52  fof(f76,plain,(
% 1.20/0.52    k3_xboole_0(k2_tarski(sK0,sK2),sK1) = k4_xboole_0(k2_tarski(sK0,sK2),k1_tarski(sK2)) | spl3_1),
% 1.20/0.52    inference(superposition,[],[f30,f70])).
% 1.20/0.52  fof(f70,plain,(
% 1.20/0.52    k1_tarski(sK2) = k4_xboole_0(k2_tarski(sK0,sK2),sK1) | spl3_1),
% 1.20/0.52    inference(forward_demodulation,[],[f69,f22])).
% 1.20/0.52  fof(f22,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f3])).
% 1.20/0.52  fof(f3,axiom,(
% 1.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.20/0.52  fof(f69,plain,(
% 1.20/0.52    k1_tarski(sK2) = k4_xboole_0(k2_tarski(sK2,sK0),sK1) | spl3_1),
% 1.20/0.52    inference(resolution,[],[f43,f35])).
% 1.20/0.52  fof(f35,plain,(
% 1.20/0.52    ~r2_hidden(sK2,sK1) | spl3_1),
% 1.20/0.52    inference(avatar_component_clause,[],[f33])).
% 1.20/0.52  fof(f43,plain,(
% 1.20/0.52    ( ! [X1] : (r2_hidden(X1,sK1) | k1_tarski(X1) = k4_xboole_0(k2_tarski(X1,sK0),sK1)) )),
% 1.20/0.52    inference(resolution,[],[f18,f26])).
% 1.20/0.52  fof(f26,plain,(
% 1.20/0.52    ( ! [X2,X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.20/0.52    inference(cnf_transformation,[],[f17])).
% 1.20/0.52  fof(f17,plain,(
% 1.20/0.52    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | (X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2)) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.20/0.52    inference(flattening,[],[f16])).
% 1.20/0.52  fof(f16,plain,(
% 1.20/0.52    ! [X0,X1,X2] : ((k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ((X0 != X1 & ~r2_hidden(X1,X2)) | r2_hidden(X0,X2))) & (((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 1.20/0.52    inference(nnf_transformation,[],[f6])).
% 1.20/0.52  fof(f6,axiom,(
% 1.20/0.52    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 1.20/0.52  fof(f30,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.20/0.52    inference(cnf_transformation,[],[f2])).
% 1.20/0.52  fof(f2,axiom,(
% 1.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.20/0.52  fof(f29,plain,(
% 1.20/0.52    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) | X0 = X1) )),
% 1.20/0.52    inference(cnf_transformation,[],[f13])).
% 1.20/0.52  fof(f13,plain,(
% 1.20/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)) | X0 = X1)),
% 1.20/0.52    inference(ennf_transformation,[],[f7])).
% 1.20/0.52  fof(f7,axiom,(
% 1.20/0.52    ! [X0,X1] : (X0 != X1 => k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),k1_tarski(X1)))),
% 1.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_zfmisc_1)).
% 1.20/0.52  fof(f40,plain,(
% 1.20/0.52    ~spl3_1 | spl3_2),
% 1.20/0.52    inference(avatar_split_clause,[],[f19,f37,f33])).
% 1.20/0.52  fof(f19,plain,(
% 1.20/0.52    sK0 = sK2 | ~r2_hidden(sK2,sK1)),
% 1.20/0.52    inference(cnf_transformation,[],[f15])).
% 1.20/0.52  % SZS output end Proof for theBenchmark
% 1.20/0.52  % (21870)------------------------------
% 1.20/0.52  % (21870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.20/0.52  % (21870)Termination reason: Refutation
% 1.20/0.52  
% 1.20/0.52  % (21870)Memory used [KB]: 10746
% 1.20/0.52  % (21870)Time elapsed: 0.104 s
% 1.20/0.52  % (21870)------------------------------
% 1.20/0.52  % (21870)------------------------------
% 1.20/0.52  % (21857)Success in time 0.156 s
%------------------------------------------------------------------------------
