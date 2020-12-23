%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   36 (  43 expanded)
%              Number of leaves         :    9 (  13 expanded)
%              Depth                    :    8
%              Number of atoms          :   76 (  92 expanded)
%              Number of equality atoms :   21 (  28 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f86,f98])).

fof(f98,plain,(
    ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f97])).

fof(f97,plain,
    ( $false
    | ~ spl3_3 ),
    inference(resolution,[],[f95,f16])).

% (25650)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f16,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r2_hidden(sK0,sK2)
    & k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(f95,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f93,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f93,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f90])).

fof(f90,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_3 ),
    inference(superposition,[],[f20,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_3
  <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f86,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f83,f17])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f83,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_4
  <=> r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f84,plain,
    ( spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f56,f81,f77])).

fof(f56,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))
    | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f19,f25])).

fof(f25,plain,(
    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f15,f18])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f15,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:38:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.43  % (25646)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.44  % (25646)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f99,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f84,f86,f98])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    ~spl3_3),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f97])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    $false | ~spl3_3),
% 0.20/0.45    inference(resolution,[],[f95,f16])).
% 0.20/0.45  % (25650)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ~r2_hidden(sK0,sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ~r2_hidden(sK0,sK2) & k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)) => (~r2_hidden(sK0,sK2) & k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 0.20/0.45    inference(negated_conjecture,[],[f6])).
% 0.20/0.45  fof(f6,conjecture,(
% 0.20/0.45    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).
% 0.20/0.45  fof(f95,plain,(
% 0.20/0.45    r2_hidden(sK0,sK2) | ~spl3_3),
% 0.20/0.45    inference(resolution,[],[f93,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.45    inference(flattening,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.45    inference(nnf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    r1_tarski(k2_tarski(sK0,sK1),sK2) | ~spl3_3),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f90])).
% 0.20/0.45  fof(f90,plain,(
% 0.20/0.45    k1_xboole_0 != k1_xboole_0 | r1_tarski(k2_tarski(sK0,sK1),sK2) | ~spl3_3),
% 0.20/0.45    inference(superposition,[],[f20,f79])).
% 0.20/0.45  fof(f79,plain,(
% 0.20/0.45    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_3),
% 0.20/0.45    inference(avatar_component_clause,[],[f77])).
% 0.20/0.45  fof(f77,plain,(
% 0.20/0.45    spl3_3 <=> k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.45    inference(nnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.20/0.45  fof(f86,plain,(
% 0.20/0.45    spl3_4),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f85])).
% 0.20/0.45  fof(f85,plain,(
% 0.20/0.45    $false | spl3_4),
% 0.20/0.45    inference(resolution,[],[f83,f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    ~r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) | spl3_4),
% 0.20/0.45    inference(avatar_component_clause,[],[f81])).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    spl3_4 <=> r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.45  fof(f84,plain,(
% 0.20/0.45    spl3_3 | ~spl3_4),
% 0.20/0.45    inference(avatar_split_clause,[],[f56,f81,f77])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    ~r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),sK2),k2_tarski(sK0,sK1)) | k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.45    inference(superposition,[],[f19,f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.20/0.45    inference(definition_unfolding,[],[f15,f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (25646)------------------------------
% 0.20/0.45  % (25646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (25646)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (25646)Memory used [KB]: 6140
% 0.20/0.45  % (25646)Time elapsed: 0.007 s
% 0.20/0.45  % (25646)------------------------------
% 0.20/0.45  % (25646)------------------------------
% 0.20/0.46  % (25643)Success in time 0.092 s
%------------------------------------------------------------------------------
