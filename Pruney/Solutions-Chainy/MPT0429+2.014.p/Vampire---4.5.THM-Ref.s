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
% DateTime   : Thu Dec  3 12:46:45 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   32 (  37 expanded)
%              Number of leaves         :    9 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   86 (  96 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f39])).

fof(f39,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f37])).

fof(f37,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f35,f15])).

fof(f15,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f35,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_3
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f36,plain,
    ( ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f32,f29,f34])).

fof(f29,plain,
    ( spl2_2
  <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f32,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl2_2 ),
    inference(resolution,[],[f30,f21])).

fof(f21,plain,(
    ! [X0,X3] :
      ( r2_hidden(X3,k1_zfmisc_1(X0))
      | ~ r1_tarski(X3,X0) ) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r1_tarski(X3,X0)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f12])).

fof(f12,plain,(
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

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f10,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

% (19613)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f30,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f31,plain,
    ( ~ spl2_2
    | spl2_1 ),
    inference(avatar_split_clause,[],[f27,f24,f29])).

fof(f24,plain,
    ( spl2_1
  <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f27,plain,
    ( ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))
    | spl2_1 ),
    inference(resolution,[],[f16,f25])).

fof(f25,plain,
    ( ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f26,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f14,f24])).

fof(f14,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).

fof(f8,plain,
    ( ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))
   => ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.36  % Computer   : n007.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % WCLimit    : 600
% 0.14/0.36  % DateTime   : Tue Dec  1 11:32:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.44  % (19601)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.23/0.45  % (19609)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.23/0.45  % (19601)Refutation found. Thanks to Tanya!
% 0.23/0.45  % SZS status Theorem for theBenchmark
% 0.23/0.45  % SZS output start Proof for theBenchmark
% 0.23/0.45  fof(f40,plain,(
% 0.23/0.45    $false),
% 0.23/0.45    inference(avatar_sat_refutation,[],[f26,f31,f36,f39])).
% 0.23/0.45  fof(f39,plain,(
% 0.23/0.45    spl2_3),
% 0.23/0.45    inference(avatar_contradiction_clause,[],[f37])).
% 0.23/0.45  fof(f37,plain,(
% 0.23/0.45    $false | spl2_3),
% 0.23/0.45    inference(resolution,[],[f35,f15])).
% 0.23/0.45  fof(f15,plain,(
% 0.23/0.45    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f1])).
% 0.23/0.45  fof(f1,axiom,(
% 0.23/0.45    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.23/0.45  fof(f35,plain,(
% 0.23/0.45    ~r1_tarski(k1_xboole_0,sK0) | spl2_3),
% 0.23/0.45    inference(avatar_component_clause,[],[f34])).
% 0.23/0.45  fof(f34,plain,(
% 0.23/0.45    spl2_3 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.23/0.45  fof(f36,plain,(
% 0.23/0.45    ~spl2_3 | spl2_2),
% 0.23/0.45    inference(avatar_split_clause,[],[f32,f29,f34])).
% 0.23/0.45  fof(f29,plain,(
% 0.23/0.45    spl2_2 <=> r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.23/0.45  fof(f32,plain,(
% 0.23/0.45    ~r1_tarski(k1_xboole_0,sK0) | spl2_2),
% 0.23/0.45    inference(resolution,[],[f30,f21])).
% 0.23/0.45  fof(f21,plain,(
% 0.23/0.45    ( ! [X0,X3] : (r2_hidden(X3,k1_zfmisc_1(X0)) | ~r1_tarski(X3,X0)) )),
% 0.23/0.45    inference(equality_resolution,[],[f18])).
% 0.23/0.45  fof(f18,plain,(
% 0.23/0.45    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r1_tarski(X3,X0) | k1_zfmisc_1(X0) != X1) )),
% 0.23/0.45    inference(cnf_transformation,[],[f13])).
% 0.23/0.45  fof(f13,plain,(
% 0.23/0.45    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f12])).
% 0.23/0.45  fof(f12,plain,(
% 0.23/0.45    ! [X1,X0] : (? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1))) => ((~r1_tarski(sK1(X0,X1),X0) | ~r2_hidden(sK1(X0,X1),X1)) & (r1_tarski(sK1(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1))))),
% 0.23/0.45    introduced(choice_axiom,[])).
% 0.23/0.45  fof(f11,plain,(
% 0.23/0.45    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | ~r1_tarski(X3,X0)) & (r1_tarski(X3,X0) | ~r2_hidden(X3,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.45    inference(rectify,[],[f10])).
% 0.23/0.45  fof(f10,plain,(
% 0.23/0.45    ! [X0,X1] : ((k1_zfmisc_1(X0) = X1 | ? [X2] : ((~r1_tarski(X2,X0) | ~r2_hidden(X2,X1)) & (r1_tarski(X2,X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ~r1_tarski(X2,X0)) & (r1_tarski(X2,X0) | ~r2_hidden(X2,X1))) | k1_zfmisc_1(X0) != X1))),
% 0.23/0.45    inference(nnf_transformation,[],[f2])).
% 0.23/0.45  fof(f2,axiom,(
% 0.23/0.45    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 0.23/0.45  % (19613)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.23/0.45  fof(f30,plain,(
% 0.23/0.45    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | spl2_2),
% 0.23/0.45    inference(avatar_component_clause,[],[f29])).
% 0.23/0.45  fof(f31,plain,(
% 0.23/0.45    ~spl2_2 | spl2_1),
% 0.23/0.45    inference(avatar_split_clause,[],[f27,f24,f29])).
% 0.23/0.45  fof(f24,plain,(
% 0.23/0.45    spl2_1 <=> m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.23/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.23/0.45  fof(f27,plain,(
% 0.23/0.45    ~r2_hidden(k1_xboole_0,k1_zfmisc_1(sK0)) | spl2_1),
% 0.23/0.45    inference(resolution,[],[f16,f25])).
% 0.23/0.45  fof(f25,plain,(
% 0.23/0.45    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0))) | spl2_1),
% 0.23/0.45    inference(avatar_component_clause,[],[f24])).
% 0.23/0.45  fof(f16,plain,(
% 0.23/0.45    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 0.23/0.45    inference(cnf_transformation,[],[f7])).
% 0.23/0.45  fof(f7,plain,(
% 0.23/0.45    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.23/0.45    inference(ennf_transformation,[],[f3])).
% 0.23/0.45  fof(f3,axiom,(
% 0.23/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.23/0.45  fof(f26,plain,(
% 0.23/0.45    ~spl2_1),
% 0.23/0.45    inference(avatar_split_clause,[],[f14,f24])).
% 0.23/0.45  fof(f14,plain,(
% 0.23/0.45    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.23/0.45    inference(cnf_transformation,[],[f9])).
% 0.23/0.45  fof(f9,plain,(
% 0.23/0.45    ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.23/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).
% 0.23/0.45  fof(f8,plain,(
% 0.23/0.45    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0))) => ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(sK0)))),
% 0.23/0.45    introduced(choice_axiom,[])).
% 0.23/0.45  fof(f6,plain,(
% 0.23/0.45    ? [X0] : ~m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.23/0.45    inference(ennf_transformation,[],[f5])).
% 0.23/0.45  fof(f5,negated_conjecture,(
% 0.23/0.45    ~! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.23/0.45    inference(negated_conjecture,[],[f4])).
% 0.23/0.45  fof(f4,conjecture,(
% 0.23/0.45    ! [X0] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(X0)))),
% 0.23/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_setfam_1)).
% 0.23/0.45  % SZS output end Proof for theBenchmark
% 0.23/0.45  % (19601)------------------------------
% 0.23/0.45  % (19601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.45  % (19601)Termination reason: Refutation
% 0.23/0.45  
% 0.23/0.45  % (19601)Memory used [KB]: 10618
% 0.23/0.45  % (19601)Time elapsed: 0.038 s
% 0.23/0.45  % (19601)------------------------------
% 0.23/0.45  % (19601)------------------------------
% 0.23/0.45  % (19594)Success in time 0.075 s
%------------------------------------------------------------------------------
