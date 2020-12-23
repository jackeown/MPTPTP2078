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
% DateTime   : Thu Dec  3 12:39:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   45 (  69 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   95 ( 140 expanded)
%              Number of equality atoms :   15 (  35 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f55,f60])).

fof(f60,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f59])).

fof(f59,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f57,f38])).

fof(f38,plain,(
    ! [X0] : ~ r1_tarski(k1_enumset1(sK0,sK0,X0),sK2) ),
    inference(resolution,[],[f18,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k1_enumset1(X0,X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f19,f27])).

fof(f27,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
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
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f18,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f57,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f35,f47])).

fof(f47,plain,
    ( sK2 = k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_1
  <=> sK2 = k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f26,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f55,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f53,f37])).

fof(f37,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f53,plain,
    ( ~ r1_tarski(sK2,sK2)
    | spl3_2 ),
    inference(resolution,[],[f51,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1)))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f29])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f51,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl3_2
  <=> r1_tarski(sK2,k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f52,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f40,f49,f45])).

fof(f40,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)))
    | sK2 = k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)) ),
    inference(resolution,[],[f30,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f17,f29,f27])).

fof(f17,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 15:34:48 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (27503)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.47  % (27525)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.48  % (27517)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.48  % (27525)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (27509)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.48  % (27517)Refutation not found, incomplete strategy% (27517)------------------------------
% 0.20/0.48  % (27517)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (27511)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.49  % (27517)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (27517)Memory used [KB]: 10618
% 0.20/0.49  % (27517)Time elapsed: 0.084 s
% 0.20/0.49  % (27517)------------------------------
% 0.20/0.49  % (27517)------------------------------
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f52,f55,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ~spl3_1),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    $false | ~spl3_1),
% 0.20/0.49    inference(subsumption_resolution,[],[f57,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k1_enumset1(sK0,sK0,X0),sK2)) )),
% 0.20/0.49    inference(resolution,[],[f18,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k1_enumset1(X0,X0,X1),X2)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f19,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.49    inference(nnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ~r2_hidden(sK0,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.20/0.49    inference(negated_conjecture,[],[f7])).
% 0.20/0.49  fof(f7,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    r1_tarski(k1_enumset1(sK0,sK0,sK1),sK2) | ~spl3_1),
% 0.20/0.49    inference(superposition,[],[f35,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    sK2 = k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    spl3_1 <=> sK2 = k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f26,f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f28,f27])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    spl3_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    $false | spl3_2),
% 0.20/0.49    inference(subsumption_resolution,[],[f53,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ~r1_tarski(sK2,sK2) | spl3_2),
% 0.20/0.49    inference(resolution,[],[f51,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X2,X2,X1))) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f22,f29])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ~r1_tarski(sK2,k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    spl3_2 <=> r1_tarski(sK2,k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f40,f49,f45])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ~r1_tarski(sK2,k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))) | sK2 = k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2))),
% 0.20/0.49    inference(resolution,[],[f30,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK1),sK2)),sK2)),
% 0.20/0.49    inference(definition_unfolding,[],[f17,f29,f27])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (27525)------------------------------
% 0.20/0.49  % (27525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (27525)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (27525)Memory used [KB]: 10618
% 0.20/0.49  % (27525)Time elapsed: 0.088 s
% 0.20/0.49  % (27525)------------------------------
% 0.20/0.49  % (27525)------------------------------
% 0.20/0.49  % (27500)Success in time 0.136 s
%------------------------------------------------------------------------------
