%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  76 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  112 ( 149 expanded)
%              Number of equality atoms :   21 (  32 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f48,f76,f80,f91,f95])).

fof(f95,plain,
    ( spl2_1
    | ~ spl2_6 ),
    inference(avatar_contradiction_clause,[],[f92])).

fof(f92,plain,
    ( $false
    | spl2_1
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f42,f90,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_enumset1(X0,X0,X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(definition_unfolding,[],[f21,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f29,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f90,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_6
  <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f42,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f91,plain,
    ( spl2_6
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f85,f69,f88])).

fof(f69,plain,
    ( spl2_4
  <=> sK1 = k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f85,plain,
    ( r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ spl2_4 ),
    inference(superposition,[],[f50,f71])).

fof(f71,plain,
    ( sK1 = k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f69])).

fof(f50,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f80,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | spl2_5 ),
    inference(unit_resulting_resolution,[],[f26,f75])).

fof(f75,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f73])).

% (1882)Refutation not found, incomplete strategy% (1882)------------------------------
% (1882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1882)Termination reason: Refutation not found, incomplete strategy

% (1882)Memory used [KB]: 6140
% (1882)Time elapsed: 0.111 s
% (1882)------------------------------
% (1882)------------------------------
fof(f73,plain,
    ( spl2_5
  <=> r1_tarski(sK1,k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f76,plain,
    ( spl2_4
    | ~ spl2_5
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f64,f45,f73,f69])).

fof(f45,plain,
    ( spl2_2
  <=> r1_tarski(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f64,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | sK1 = k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f63,f27])).

fof(f63,plain,
    ( sK1 = k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r1_tarski(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f61,f27])).

fof(f61,plain,
    ( sK1 = k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)
    | ~ r1_tarski(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f25,f47])).

fof(f47,plain,
    ( r1_tarski(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f48,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f33,f45])).

fof(f33,plain,(
    r1_tarski(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1) ),
    inference(definition_unfolding,[],[f18,f32])).

fof(f32,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f31])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f18,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f43,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f19,f40])).

fof(f19,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:15:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (1862)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (1859)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.50  % (1879)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (1871)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (1860)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (1863)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (1879)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (1858)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (1882)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f43,f48,f76,f80,f91,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl2_1 | ~spl2_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    $false | (spl2_1 | ~spl2_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f42,f90,f35])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_enumset1(X0,X0,X0,X1),X2) | r2_hidden(X1,X2)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f21,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f29,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.51    inference(flattening,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.21/0.51    inference(nnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl2_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl2_6 <=> r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ~r2_hidden(sK0,sK1) | spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    spl2_1 <=> r2_hidden(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    spl2_6 | ~spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f85,f69,f88])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl2_4 <=> sK1 = k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    r1_tarski(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~spl2_4),
% 0.21/0.51    inference(superposition,[],[f50,f71])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    sK1 = k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl2_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f69])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(superposition,[],[f26,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    spl2_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f77])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    $false | spl2_5),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f26,f75])).
% 0.21/0.51  fof(f75,plain,(
% 0.21/0.51    ~r1_tarski(sK1,k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f73])).
% 0.21/0.51  % (1882)Refutation not found, incomplete strategy% (1882)------------------------------
% 0.21/0.51  % (1882)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1882)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1882)Memory used [KB]: 6140
% 0.21/0.51  % (1882)Time elapsed: 0.111 s
% 0.21/0.51  % (1882)------------------------------
% 0.21/0.51  % (1882)------------------------------
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    spl2_5 <=> r1_tarski(sK1,k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl2_4 | ~spl2_5 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f64,f45,f73,f69])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    spl2_2 <=> r1_tarski(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    ~r1_tarski(sK1,k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | sK1 = k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl2_2),
% 0.21/0.52    inference(forward_demodulation,[],[f63,f27])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    sK1 = k2_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r1_tarski(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~spl2_2),
% 0.21/0.52    inference(forward_demodulation,[],[f61,f27])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    sK1 = k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1) | ~r1_tarski(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)) | ~spl2_2),
% 0.21/0.52    inference(resolution,[],[f25,f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    r1_tarski(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1) | ~spl2_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f45])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    spl2_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f33,f45])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    r1_tarski(k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),sK1)),
% 0.21/0.52    inference(definition_unfolding,[],[f18,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f28,f31])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f11,plain,(
% 0.21/0.52    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f9])).
% 0.21/0.52  fof(f9,conjecture,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    ~spl2_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f19,f40])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ~r2_hidden(sK0,sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f13])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (1879)------------------------------
% 0.21/0.52  % (1879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1879)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (1879)Memory used [KB]: 10746
% 0.21/0.52  % (1879)Time elapsed: 0.107 s
% 0.21/0.52  % (1879)------------------------------
% 0.21/0.52  % (1879)------------------------------
% 0.21/0.52  % (1855)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (1856)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (1856)Refutation not found, incomplete strategy% (1856)------------------------------
% 0.21/0.52  % (1856)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (1856)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (1856)Memory used [KB]: 1663
% 0.21/0.52  % (1856)Time elapsed: 0.116 s
% 0.21/0.52  % (1856)------------------------------
% 0.21/0.52  % (1856)------------------------------
% 0.21/0.52  % (1854)Success in time 0.16 s
%------------------------------------------------------------------------------
