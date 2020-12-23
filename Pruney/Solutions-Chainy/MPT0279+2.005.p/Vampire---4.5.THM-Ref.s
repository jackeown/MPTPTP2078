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
% DateTime   : Thu Dec  3 12:41:34 EST 2020

% Result     : Theorem 1.25s
% Output     : Refutation 1.25s
% Verified   : 
% Statistics : Number of formulae       :   37 (  40 expanded)
%              Number of leaves         :    9 (  12 expanded)
%              Depth                    :    9
%              Number of atoms          :  115 ( 121 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f64,f69])).

fof(f69,plain,(
    spl2_2 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl2_2 ),
    inference(subsumption_resolution,[],[f66,f32])).

fof(f32,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f66,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl2_2 ),
    inference(resolution,[],[f63,f30])).

fof(f30,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ( ( ~ r1_tarski(sK1(X0,X1),X0)
            | ~ r2_hidden(sK1(X0,X1),X1) )
          & ( r1_tarski(sK1(X0,X1),X0)
            | r2_hidden(sK1(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X2,X0)
            | ~ r2_hidden(X2,X1) )
          & ( r1_tarski(X2,X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ~ r1_tarski(sK1(X0,X1),X0)
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( r1_tarski(sK1(X0,X1),X0)
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r1_tarski(X3,X0) )
            & ( r1_tarski(X3,X0)
              | ~ r2_hidden(X3,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_zfmisc_1(X0) = X1
        | ? [X2] :
            ( ( ~ r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) )
            & ( r1_tarski(X2,X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ~ r1_tarski(X2,X0) )
            & ( r1_tarski(X2,X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_zfmisc_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f63,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl2_2
  <=> r2_hidden(sK0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f64,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f57,f35,f61])).

fof(f35,plain,
    ( spl2_1
  <=> r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f57,plain,
    ( ~ r2_hidden(sK0,k1_zfmisc_1(sK0))
    | spl2_1 ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(superposition,[],[f21,f29])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f38,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).

fof(f8,plain,
    ( ? [X0] : ~ r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))
   => ~ r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] : ~ r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:31:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (8196)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.51  % (8214)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (8206)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.25/0.52  % (8201)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.25/0.52  % (8189)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.25/0.52  % (8189)Refutation not found, incomplete strategy% (8189)------------------------------
% 1.25/0.52  % (8189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (8189)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.52  
% 1.25/0.52  % (8189)Memory used [KB]: 1663
% 1.25/0.52  % (8189)Time elapsed: 0.099 s
% 1.25/0.52  % (8189)------------------------------
% 1.25/0.52  % (8189)------------------------------
% 1.25/0.52  % (8209)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.25/0.52  % (8209)Refutation found. Thanks to Tanya!
% 1.25/0.52  % SZS status Theorem for theBenchmark
% 1.25/0.52  % SZS output start Proof for theBenchmark
% 1.25/0.52  fof(f70,plain,(
% 1.25/0.52    $false),
% 1.25/0.52    inference(avatar_sat_refutation,[],[f38,f64,f69])).
% 1.25/0.52  fof(f69,plain,(
% 1.25/0.52    spl2_2),
% 1.25/0.52    inference(avatar_contradiction_clause,[],[f68])).
% 1.25/0.52  fof(f68,plain,(
% 1.25/0.52    $false | spl2_2),
% 1.25/0.52    inference(subsumption_resolution,[],[f66,f32])).
% 1.25/0.52  fof(f32,plain,(
% 1.25/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.25/0.52    inference(equality_resolution,[],[f27])).
% 1.25/0.52  fof(f27,plain,(
% 1.25/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.25/0.52    inference(cnf_transformation,[],[f17])).
% 1.25/0.52  fof(f17,plain,(
% 1.25/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.25/0.52    inference(flattening,[],[f16])).
% 1.25/0.52  fof(f16,plain,(
% 1.25/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.25/0.52    inference(nnf_transformation,[],[f1])).
% 1.25/0.52  fof(f1,axiom,(
% 1.25/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.25/0.52  fof(f66,plain,(
% 1.25/0.52    ~r1_tarski(sK0,sK0) | spl2_2),
% 1.25/0.52    inference(resolution,[],[f63,f30])).
% 1.25/0.52  fof(f30,plain,(
% 1.25/0.52    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 1.25/0.52    inference(equality_resolution,[],[f23])).
% 1.25/0.52  fof(f23,plain,(
% 1.25/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 1.25/0.52    inference(cnf_transformation,[],[f15])).
% 1.25/0.52  fof(f15,plain,(
% 1.25/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.25/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f14])).
% 1.25/0.52  fof(f14,plain,(
% 1.25/0.52    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 1.25/0.52    introduced(choice_axiom,[])).
% 1.25/0.52  fof(f13,plain,(
% 1.25/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.25/0.52    inference(rectify,[],[f12])).
% 1.25/0.52  fof(f12,plain,(
% 1.25/0.52    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 1.25/0.52    inference(nnf_transformation,[],[f3])).
% 1.25/0.52  fof(f3,axiom,(
% 1.25/0.52    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 1.25/0.52  fof(f63,plain,(
% 1.25/0.52    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | spl2_2),
% 1.25/0.52    inference(avatar_component_clause,[],[f61])).
% 1.25/0.52  fof(f61,plain,(
% 1.25/0.52    spl2_2 <=> r2_hidden(sK0,k1_zfmisc_1(sK0))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.25/0.52  fof(f64,plain,(
% 1.25/0.52    ~spl2_2 | spl2_1),
% 1.25/0.52    inference(avatar_split_clause,[],[f57,f35,f61])).
% 1.25/0.52  fof(f35,plain,(
% 1.25/0.52    spl2_1 <=> r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0))),
% 1.25/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.25/0.52  fof(f57,plain,(
% 1.25/0.52    ~r2_hidden(sK0,k1_zfmisc_1(sK0)) | spl2_1),
% 1.25/0.52    inference(resolution,[],[f50,f37])).
% 1.25/0.52  fof(f37,plain,(
% 1.25/0.52    ~r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0)) | spl2_1),
% 1.25/0.52    inference(avatar_component_clause,[],[f35])).
% 1.25/0.52  fof(f50,plain,(
% 1.25/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.25/0.52    inference(duplicate_literal_removal,[],[f49])).
% 1.25/0.52  fof(f49,plain,(
% 1.25/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.25/0.52    inference(superposition,[],[f21,f29])).
% 1.25/0.52  fof(f29,plain,(
% 1.25/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f2])).
% 1.25/0.52  fof(f2,axiom,(
% 1.25/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.25/0.52  fof(f21,plain,(
% 1.25/0.52    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.25/0.52    inference(cnf_transformation,[],[f11])).
% 1.25/0.52  fof(f11,plain,(
% 1.25/0.52    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.25/0.52    inference(flattening,[],[f10])).
% 1.25/0.52  fof(f10,plain,(
% 1.25/0.52    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.25/0.52    inference(nnf_transformation,[],[f4])).
% 1.25/0.52  fof(f4,axiom,(
% 1.25/0.52    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.25/0.52  fof(f38,plain,(
% 1.25/0.52    ~spl2_1),
% 1.25/0.52    inference(avatar_split_clause,[],[f18,f35])).
% 1.25/0.52  fof(f18,plain,(
% 1.25/0.52    ~r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0))),
% 1.25/0.52    inference(cnf_transformation,[],[f9])).
% 1.25/0.52  fof(f9,plain,(
% 1.25/0.52    ~r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0))),
% 1.25/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f8])).
% 1.25/0.52  fof(f8,plain,(
% 1.25/0.52    ? [X0] : ~r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0)) => ~r1_tarski(k1_tarski(sK0),k1_zfmisc_1(sK0))),
% 1.25/0.52    introduced(choice_axiom,[])).
% 1.25/0.52  fof(f7,plain,(
% 1.25/0.52    ? [X0] : ~r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.25/0.52    inference(ennf_transformation,[],[f6])).
% 1.25/0.52  fof(f6,negated_conjecture,(
% 1.25/0.52    ~! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.25/0.52    inference(negated_conjecture,[],[f5])).
% 1.25/0.52  fof(f5,conjecture,(
% 1.25/0.52    ! [X0] : r1_tarski(k1_tarski(X0),k1_zfmisc_1(X0))),
% 1.25/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).
% 1.25/0.52  % SZS output end Proof for theBenchmark
% 1.25/0.52  % (8209)------------------------------
% 1.25/0.52  % (8209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.52  % (8209)Termination reason: Refutation
% 1.25/0.52  
% 1.25/0.52  % (8209)Memory used [KB]: 6140
% 1.25/0.52  % (8209)Time elapsed: 0.106 s
% 1.25/0.52  % (8209)------------------------------
% 1.25/0.52  % (8209)------------------------------
% 1.25/0.53  % (8187)Success in time 0.162 s
%------------------------------------------------------------------------------
